//! Reconstructs slice indexing calls erased by MIR lowering.

use rustc_hir::def::Namespace;
use rustc_hir::lang_items::LangItem;
use rustc_middle::mir::{
    self, BasicBlock, Body, Local, Operand, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{self as mir_ty, Ty, TyCtxt};
use rustc_span::def_id::DefId;
use rustc_span::source_map::Spanned;
use rustc_span::{sym, Symbol};

use crate::analyze;
use crate::analyze::two_phase_borrow;

/// The bounds-check block emitted for an indexing expression.
struct BoundsCheck<'tcx> {
    block: BasicBlock,
    condition_local: Option<Local>,
    len: Operand<'tcx>,
    index: Operand<'tcx>,
    index_local: Local,
    target: BasicBlock,
    unwind: mir::UnwindAction,
    source_info: mir::SourceInfo,
}

/// The slice access in the target of a [`BoundsCheck`].
struct SliceAccess<'tcx> {
    indexed_place: mir::Place<'tcx>,
    /// The reference to the slice, or the array place that is borrowed and unsized to one.
    receiver: mir::Place<'tcx>,
    receiver_is_array: bool,
    receiver_mutability: mir_ty::Mutability,
    slice_ty: Ty<'tcx>,
    elem_ty: Ty<'tcx>,
    mutable: bool,
}

/// The statements and terminators that use the indexed place of a [`SliceAccess`], all reached
/// only through the bounds check.
struct AccessUses {
    locations: Vec<mir::Location>,
    /// Those of `locations` that may change the place (a write or a `&mut` borrow).
    mutating: Vec<mir::Location>,
}

/// Finds the first `(*slice)[index]` place in the blocks it visits and every use of that place.
struct IndexedPlaceFinder<'a, 'tcx> {
    body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    index: Local,
    found: Option<mir::Place<'tcx>>,
    use_locations: Vec<mir::Location>,
    mutating_locations: Vec<mir::Location>,
}

impl<'tcx> mir::visit::Visitor<'tcx> for IndexedPlaceFinder<'_, 'tcx> {
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        context: mir::visit::PlaceContext,
        location: mir::Location,
    ) {
        let Some(index_pos) = place
            .projection
            .iter()
            .position(|elem| elem == mir::PlaceElem::Index(self.index))
        else {
            return;
        };
        let indexed = mir::Place {
            local: place.local,
            projection: self
                .tcx
                .mk_place_elems(&place.projection.as_slice()[..=index_pos]),
        };
        if self.found.is_none() {
            let base = mir::Place {
                local: place.local,
                projection: self
                    .tcx
                    .mk_place_elems(&place.projection.as_slice()[..index_pos]),
            };
            if !matches!(
                base.ty(&self.body.local_decls, self.tcx).ty.kind(),
                mir_ty::TyKind::Slice(_) | mir_ty::TyKind::Array(..)
            ) {
                return;
            }
            self.found = Some(indexed);
        }
        if self.found == Some(indexed) {
            if !self.use_locations.contains(&location) {
                self.use_locations.push(location);
            }
            if context.is_mutating_use() && !self.mutating_locations.contains(&location) {
                self.mutating_locations.push(location);
            }
        }
    }
}

struct ReadFinder {
    local: Local,
    found: bool,
}

impl<'tcx> mir::visit::Visitor<'tcx> for ReadFinder {
    fn visit_local(&mut self, local: Local, context: mir::visit::PlaceContext, _: mir::Location) {
        let is_store =
            context == mir::visit::PlaceContext::MutatingUse(mir::visit::MutatingUseContext::Store);
        if local == self.local && context.is_use() && !is_store {
            self.found = true;
        }
    }
}

/// Reconstructs the trait call erased by MIR's first-class slice indexing operation.
///
/// For example, optimized MIR for `slice[index]` contains:
///
/// ```text
/// fn shared_slice_index(_1: &[i32], _2: usize) -> i32 {
///     let mut _0: i32;
///     let mut _3: usize;
///     let mut _4: bool;
///
///     bb0: {
///         _3 = PtrMetadata(copy _1);
///         _4 = Lt(copy _2, copy _3);
///         assert(move _4, "index out of bounds: the length is {} but the index is {}", move _3, copy _2) -> [success: bb1, unwind continue];
///     }
///
///     bb1: {
///         _0 = copy (*_1)[_2];
///         return;
///     }
/// }
/// ```
///
/// This reconstruction replaces that sequence with an `Index::index` or `IndexMut::index_mut`
/// call terminator and rewrites the indexed place to dereference its result:
///
/// ```text
/// fn shared_slice_index(_1: &[i32], _2: usize) -> i32 {
///     let mut _0: i32;
///     let _5: &i32;
///
///     bb0: {
///         _5 = <[i32] as Index<usize>>::index(copy _1, copy _2)
///             -> [return: bb1, unwind continue];
///     }
///
///     bb1: {
///         _0 = copy (*_5);
///         return;
///     }
/// }
/// ```
///
/// The analyzer therefore applies the registered trait-method type and remains independent of
/// the model selected for slices.
pub fn reconstruct<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    // A block split off by `reconstruct_at_activation` may end in a bounds check.
    let mut next = 0;
    while next < body.basic_blocks.len() {
        let block = BasicBlock::from_usize(next);
        next += 1;
        let Some(bounds_check) = find_bounds_check(body, block) else {
            continue;
        };
        let region = access_region(body, &bounds_check);
        let Some((access, uses)) = find_slice_access(tcx, body, &bounds_check, &region) else {
            tracing::trace!(?block, "bounds check is not followed by slice indexing");
            continue;
        };
        // The rewritten blocks use a result local defined by this block's new call. Entering the
        // target from another predecessor would leave that local undefined; the region holds
        // only blocks the target dominates.
        assert_eq!(
            body.basic_blocks.predecessors()[bounds_check.target].as_slice(),
            [block],
            "slice indexing target must have exactly one predecessor",
        );

        tracing::debug!(
            assert_block = ?block,
            target = ?bounds_check.target,
            indexed_place = ?access.indexed_place,
            receiver = ?access.receiver,
            mutable = access.mutable,
            "reconstructing a trait method call from slice indexing"
        );
        match moved_borrow(tcx, body, &access, &uses) {
            Some((reservation, creation)) => reconstruct_at_activation(
                tcx,
                body,
                bounds_check,
                access,
                &uses,
                reservation,
                creation,
            ),
            None => reconstruct_access(tcx, body, bounds_check, access, &uses),
        }
    }
}

/// The use of the access that is a two-phase `&mut` borrow which `two_phase_borrow` moves, with
/// the point where it creates the borrow. Its other uses must be reads that dominate it, such as
/// the length that the bounds check of an element it indexes further reads (`s[i][j]` of
/// `&mut [&mut [T]]`).
fn moved_borrow<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    access: &SliceAccess<'tcx>,
    uses: &AccessUses,
) -> Option<(mir::Location, mir::Location)> {
    let (reservation, creation) = uses.locations.iter().find_map(|&location| {
        two_phase_borrow::moved_creation_point(tcx, body, location)
            .map(|creation| (location, creation))
    })?;
    let dominators = body.basic_blocks.dominators();
    let is_read_before = |location: &mir::Location| {
        location.dominates(reservation, dominators) && !uses.mutating.contains(location)
    };
    assert!(
        uses.locations
            .iter()
            .all(|location| *location == reservation || is_read_before(location)),
        "two-phase borrow of {:?}: the indexed place has other uses",
        access.indexed_place
    );
    Some((reservation, creation))
}

/// Recognizes the bounds-check terminator and records the simple local used as the index.
fn find_bounds_check<'tcx>(body: &Body<'tcx>, block: BasicBlock) -> Option<BoundsCheck<'tcx>> {
    let terminator = body.basic_blocks[block].terminator.as_ref()?;
    let TerminatorKind::Assert {
        cond,
        msg,
        target,
        unwind,
        ..
    } = &terminator.kind
    else {
        return None;
    };
    let mir::AssertMessage::BoundsCheck { len, index } = &**msg else {
        return None;
    };
    let index_place = index.place()?;
    if !index_place.projection.is_empty() {
        return None;
    }

    Some(BoundsCheck {
        block,
        condition_local: cond
            .place()
            .filter(|place| place.projection.is_empty())
            .map(|place| place.local),
        len: len.clone(),
        index: index.clone(),
        index_local: index_place.local,
        target: *target,
        unwind: *unwind,
        source_info: terminator.source_info,
    })
}

/// The blocks that the bounds check's target dominates and reaches up to the next bounds check of
/// the same index, in depth-first order. The block that ends in that check belongs to the region, for
/// the statements before the check, but the blocks after it are reached through the call that
/// the check is reconstructed into.
fn access_region(body: &Body<'_>, bounds_check: &BoundsCheck<'_>) -> Vec<BasicBlock> {
    let rechecks_index = |block: BasicBlock| {
        let terminator = body.basic_blocks[block].terminator();
        let TerminatorKind::Assert { msg, .. } = &terminator.kind else {
            return false;
        };
        let mir::AssertMessage::BoundsCheck { index, .. } = &**msg else {
            return false;
        };
        index.place().is_some_and(|place| {
            place.projection.is_empty() && place.local == bounds_check.index_local
        })
    };
    let dominators = body.basic_blocks.dominators();
    let mut region = Vec::new();
    let mut stack = vec![bounds_check.target];
    while let Some(block) = stack.pop() {
        if block == bounds_check.block
            || region.contains(&block)
            || !dominators.dominates(bounds_check.target, block)
        {
            continue;
        }
        region.push(block);
        if rechecks_index(block) {
            continue;
        }
        stack.extend(body.basic_blocks[block].terminator().successors());
    }
    region
}

/// Finds the matching `(*slice)[index]` place in the blocks the bounds check guards.
fn find_slice_access<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
    region: &[BasicBlock],
) -> Option<(SliceAccess<'tcx>, AccessUses)> {
    use mir::visit::Visitor as _;

    let mut finder = IndexedPlaceFinder {
        body,
        tcx,
        index: bounds_check.index_local,
        found: None,
        use_locations: Vec::new(),
        mutating_locations: Vec::new(),
    };
    for &block in region {
        finder.visit_basic_block_data(block, &body.basic_blocks[block]);
    }
    let mutable = !finder.mutating_locations.is_empty();
    let access = slice_access(tcx, body, finder.found?, mutable)?;
    let uses = AccessUses {
        locations: finder.use_locations,
        mutating: finder.mutating_locations,
    };
    Some((access, uses))
}

/// The access to `indexed_place`, which ends in an index.
fn slice_access<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    indexed_place: mir::Place<'tcx>,
    mutable: bool,
) -> Option<SliceAccess<'tcx>> {
    // The indexed place has the shape `receiver.*[index]` of a slice, whose dereference and
    // index are stripped to recover the reference passed to `Index::index` or
    // `IndexMut::index_mut`, or `array[index]`, whose array is borrowed and unsized to a slice.
    let mut receiver_projection = indexed_place.projection.as_slice().to_vec();
    if !matches!(receiver_projection.pop(), Some(mir::PlaceElem::Index(_))) {
        return None;
    }
    let base = mir::Place {
        local: indexed_place.local,
        projection: tcx.mk_place_elems(&receiver_projection),
    };
    if let mir_ty::TyKind::Array(elem_ty, _) = base.ty(&body.local_decls, tcx).ty.kind() {
        return Some(SliceAccess {
            indexed_place,
            receiver: base,
            receiver_is_array: true,
            receiver_mutability: mutability_of(mutable),
            slice_ty: Ty::new_slice(tcx, *elem_ty),
            elem_ty: *elem_ty,
            mutable,
        });
    }
    if receiver_projection.pop() != Some(mir::PlaceElem::Deref) {
        return None;
    }
    let receiver = mir::Place {
        local: indexed_place.local,
        projection: tcx.mk_place_elems(&receiver_projection),
    };
    let mir_ty::TyKind::Ref(_, slice_ty, receiver_mutability) =
        receiver.ty(&body.local_decls, tcx).ty.kind()
    else {
        return None;
    };
    let mir_ty::TyKind::Slice(elem_ty) = slice_ty.kind() else {
        return None;
    };
    if mutable && !receiver_mutability.is_mut() {
        return None;
    }

    Some(SliceAccess {
        indexed_place,
        receiver,
        receiver_is_array: false,
        receiver_mutability: *receiver_mutability,
        slice_ty: *slice_ty,
        elem_ty: *elem_ty,
        mutable,
    })
}

fn mutability_of(mutable: bool) -> mir_ty::Mutability {
    if mutable {
        mir_ty::Mutability::Mut
    } else {
        mir_ty::Mutability::Not
    }
}

fn reconstruct_access<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    bounds_check: BoundsCheck<'tcx>,
    access: SliceAccess<'tcx>,
    uses: &AccessUses,
) {
    let result_local = insert_index_call(
        tcx,
        body,
        &bounds_check,
        &access,
        access.mutable,
        bounds_check.block,
        bounds_check.target,
    );
    replace_place_at(
        body,
        tcx,
        &uses.locations,
        access.indexed_place,
        result_local,
    );
    remove_bounds_check_setup(body, &bounds_check);
}

/// Reconstructs an access that is a two-phase `&mut` borrow `_t = &mut (*r)[i]` (an autoref'd
/// receiver) whose arguments read the sequence, as in `s[0].bump(s[1])`.
///
/// As rustc's borrow checker does, the reservation acts as a shared borrow and the mutable borrow
/// starts at the activation. Each bounds check of the borrowed place, the access's and those of
/// the elements it indexes further (`s[0][1]`), becomes an `Index::index` call, and the
/// `IndexMut::index_mut` calls and the borrow of the last result are placed where
/// `two_phase_borrow` would create the borrow, so that the reads in between see the sequence's
/// current value rather than the prophecy of the mutable borrow. The reads of the access before
/// the reservation go through the `Index::index` results.
fn reconstruct_at_activation<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    bounds_check: BoundsCheck<'tcx>,
    access: SliceAccess<'tcx>,
    uses: &AccessUses,
    reservation: mir::Location,
    creation: mir::Location,
) {
    let mut borrow = std::mem::replace(
        &mut body.basic_blocks.as_mut()[reservation.block].statements[reservation.statement_index],
        mir::Statement::new(bounds_check.source_info, StatementKind::Nop),
    );
    let Some((_, Rvalue::Ref(_, _, borrowed))) = borrow.kind.as_assign() else {
        unreachable!("two-phase borrow is not a borrow: {borrow:?}");
    };
    let borrowed = *borrowed;
    let reads: Vec<_> = uses
        .locations
        .iter()
        .copied()
        .filter(|location| *location != reservation)
        .collect();
    let levels = index_levels(body, bounds_check, &access, borrowed, reservation);

    let mut shared = None;
    for level in &levels {
        let place = level.place(tcx, borrowed, shared);
        let (block, target) = (level.check.block, level.check.target);
        let result = insert_level_call(tcx, body, level, place, false, block, target);
        replace_place_at(body, tcx, &reads, place, result);
        shared = Some((result, level.position));
    }

    let rest = split_before(body, creation);
    let mut block = creation.block;
    let mut mutable = None;
    for (i, level) in levels.iter().enumerate() {
        let place = level.place(tcx, borrowed, mutable);
        let target = if i + 1 == levels.len() {
            rest
        } else {
            let empty = mir::BasicBlockData::new(None, body.basic_blocks[block].is_cleanup);
            body.basic_blocks.as_mut().push(empty)
        };
        let result = insert_level_call(tcx, body, level, place, true, block, target);
        mutable = Some((result, level.position));
        block = target;
    }
    let (result, position) = mutable.unwrap();
    let indexed = IndexLevel::prefix(tcx, borrowed, position);
    analyze::ReplacePlacesVisitor::with_replacement(
        tcx,
        indexed,
        tcx.mk_place_deref(result.into()),
    )
    .visit_statement(&mut borrow);
    body.basic_blocks.as_mut()[rest]
        .statements
        .insert(0, borrow);
    for level in &levels {
        remove_bounds_check_setup(body, &level.check);
    }
}

/// An index of a borrowed place with the bounds check rustc emits for it.
struct IndexLevel<'tcx> {
    check: BoundsCheck<'tcx>,
    /// The position of the index in the projection of the borrowed place.
    position: usize,
}

impl<'tcx> IndexLevel<'tcx> {
    /// The place `place` names up to this index, with the part up to the previous index replaced
    /// by the dereference of `previous`, the call result for it.
    fn place(
        &self,
        tcx: TyCtxt<'tcx>,
        place: mir::Place<'tcx>,
        previous: Option<(Local, usize)>,
    ) -> mir::Place<'tcx> {
        let Some((result, previous_position)) = previous else {
            return Self::prefix(tcx, place, self.position);
        };
        let projection = &place.projection.as_slice()[previous_position + 1..=self.position];
        mir::Place {
            local: result,
            projection: tcx.mk_place_elems_from_iter(
                std::iter::once(mir::PlaceElem::Deref).chain(projection.iter().copied()),
            ),
        }
    }

    fn prefix(tcx: TyCtxt<'tcx>, place: mir::Place<'tcx>, position: usize) -> mir::Place<'tcx> {
        mir::Place {
            local: place.local,
            projection: tcx.mk_place_elems(&place.projection.as_slice()[..=position]),
        }
    }
}

/// The access's index and each further index of `borrowed` (`s[i][j]`), with its bounds check:
/// the checks of the further indices lie between the access's check and the reservation, in order.
fn index_levels<'tcx>(
    body: &Body<'tcx>,
    bounds_check: BoundsCheck<'tcx>,
    access: &SliceAccess<'tcx>,
    borrowed: mir::Place<'tcx>,
    reservation: mir::Location,
) -> Vec<IndexLevel<'tcx>> {
    let dominators = body.basic_blocks.dominators();
    let mut between = Vec::new();
    let mut block = reservation.block;
    while let Some(dominator) = dominators.immediate_dominator(block) {
        if dominator == bounds_check.block {
            break;
        }
        between.push(dominator);
        block = dominator;
    }
    let mut checks = between
        .into_iter()
        .rev()
        .filter_map(|block| find_bounds_check(body, block));

    let position = access.indexed_place.projection.len() - 1;
    let mut levels = vec![IndexLevel {
        check: bounds_check,
        position,
    }];
    for (position, elem) in borrowed.projection.iter().enumerate().skip(position + 1) {
        let mir::PlaceElem::Index(index) = elem else {
            continue;
        };
        let check = checks
            .find(|check| check.index_local == index)
            .unwrap_or_else(|| {
                panic!("two-phase borrow of {borrowed:?}: no bounds check of its index {index:?}")
            });
        levels.push(IndexLevel { check, position });
    }
    levels
}

/// Ends `block` with the `Index::index` or `IndexMut::index_mut` call for `place`, the indexed
/// place of `level`, returning to `target`, and returns the local that holds the call's result.
fn insert_level_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    level: &IndexLevel<'tcx>,
    place: mir::Place<'tcx>,
    mutable: bool,
    block: BasicBlock,
    target: BasicBlock,
) -> Local {
    let access = slice_access(tcx, body, place, mutable)
        .unwrap_or_else(|| panic!("{place:?} is not an indexed sequence"));
    insert_index_call(tcx, body, &level.check, &access, mutable, block, target)
}

/// Replaces `from` with the dereference of `result` in the statements and terminators at
/// `locations`.
fn replace_place_at<'tcx>(
    body: &mut Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    locations: &[mir::Location],
    from: mir::Place<'tcx>,
    result: Local,
) {
    let mut replacer = analyze::ReplacePlacesVisitor::with_replacement(
        tcx,
        from,
        tcx.mk_place_deref(result.into()),
    );
    for location in locations {
        let data = &mut body.basic_blocks.as_mut()[location.block];
        match data.statements.get_mut(location.statement_index) {
            Some(statement) => replacer.visit_statement(statement),
            None => replacer.visit_terminator(data.terminator_mut()),
        }
    }
}

/// Moves the statements of `location`'s block from `location` on, and its terminator, to a new
/// block, which is returned; the caller ends the old block with a jump to it.
fn split_before(body: &mut Body<'_>, location: mir::Location) -> BasicBlock {
    let blocks = body.basic_blocks.as_mut();
    let data = &mut blocks[location.block];
    let statements = data.statements.split_off(location.statement_index);
    let terminator = data.terminator.take();
    let is_cleanup = data.is_cleanup;
    blocks.push(mir::BasicBlockData::new_stmts(
        statements, terminator, is_cleanup,
    ))
}

/// Ends `block` with the `Index::index` or `IndexMut::index_mut` call for the access, returning
/// to `target`, and returns the local that holds the call's result.
fn insert_index_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
    access: &SliceAccess<'tcx>,
    mutable: bool,
    block: BasicBlock,
    target: BasicBlock,
) -> Local {
    let region = mir_ty::Region::new_from_kind(tcx, mir_ty::RegionKind::ReErased);
    let result_ty = mir_ty::Ty::new_ref(tcx, region, access.elem_ty, mutability_of(mutable));
    let result_local = body
        .local_decls
        .push(mir::LocalDecl::new(result_ty, bounds_check.source_info.span).immutable());
    let receiver = receiver_operand(tcx, body, bounds_check, access, mutable, block, region);

    let (lang_item, method_name) = if mutable {
        (LangItem::IndexMut, sym::index_mut)
    } else {
        (LangItem::Index, sym::index)
    };
    let method = lang_item_method(tcx, lang_item, method_name);
    let args = tcx.mk_args(&[access.slice_ty.into(), tcx.types.usize.into()]);
    let func = super::fn_operand(tcx, method, args, bounds_check.source_info.span);
    let call_args = [receiver, bounds_check.index.clone()]
        .into_iter()
        .map(|node| Spanned {
            node,
            span: bounds_check.source_info.span,
        })
        .collect::<Vec<_>>()
        .into_boxed_slice();

    body.basic_blocks.as_mut()[block].terminator = Some(mir::Terminator {
        source_info: bounds_check.source_info,
        kind: TerminatorKind::Call {
            func,
            args: call_args,
            destination: result_local.into(),
            target: Some(target),
            unwind: bounds_check.unwind,
            call_source: mir::CallSource::Normal,
            fn_span: bounds_check.source_info.span,
        },
    });
    tracing::trace!(?result_local, ?method, "slice indexing call inserted");
    result_local
}

/// Builds the receiver operand, inserting at the end of `block` a shared reborrow when indexing
/// through `&mut [T]`.
fn receiver_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
    access: &SliceAccess<'tcx>,
    mutable: bool,
    block: BasicBlock,
    region: mir_ty::Region<'tcx>,
) -> Operand<'tcx> {
    if access.receiver_is_array {
        return array_receiver_operand(tcx, body, bounds_check, access, mutable, block, region);
    }
    if !mutable && access.receiver_mutability.is_mut() {
        let ty = mir_ty::Ty::new_ref(tcx, region, access.slice_ty, mir_ty::Mutability::Not);
        let local = body
            .local_decls
            .push(mir::LocalDecl::new(ty, bounds_check.source_info.span).immutable());
        body.basic_blocks.as_mut()[block]
            .statements
            .push(mir::Statement::new(
                bounds_check.source_info,
                StatementKind::Assign(Box::new((
                    local.into(),
                    Rvalue::Ref(
                        region,
                        mir::BorrowKind::Shared,
                        tcx.mk_place_deref(access.receiver),
                    ),
                ))),
            ));
        Operand::Copy(local.into())
    } else if mutable {
        Operand::Move(access.receiver)
    } else {
        Operand::Copy(access.receiver)
    }
}

/// Borrows the indexed array at the end of `block` and unsizes the borrow to a slice reference,
/// as `array[index]` does through `[T; N]`'s `Index` impl.
fn array_receiver_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
    access: &SliceAccess<'tcx>,
    mutable: bool,
    block: BasicBlock,
    region: mir_ty::Region<'tcx>,
) -> Operand<'tcx> {
    let span = bounds_check.source_info.span;
    let mutability = mutability_of(mutable);
    let array_ref_ty = Ty::new_ref(
        tcx,
        region,
        access.receiver.ty(&body.local_decls, tcx).ty,
        mutability,
    );
    let slice_ref_ty = Ty::new_ref(tcx, region, access.slice_ty, mutability);
    let array_ref = body
        .local_decls
        .push(mir::LocalDecl::new(array_ref_ty, span).immutable());
    let slice_ref = body
        .local_decls
        .push(mir::LocalDecl::new(slice_ref_ty, span).immutable());
    let borrow_kind = if mutable {
        mir::BorrowKind::Mut {
            kind: mir::MutBorrowKind::Default,
        }
    } else {
        mir::BorrowKind::Shared
    };
    let unsize = mir::CastKind::PointerCoercion(
        mir_ty::adjustment::PointerCoercion::Unsize,
        mir::CoercionSource::Implicit,
    );
    let statements = [
        (array_ref, Rvalue::Ref(region, borrow_kind, access.receiver)),
        (
            slice_ref,
            Rvalue::Cast(unsize, Operand::Move(array_ref.into()), slice_ref_ty),
        ),
    ];
    for (local, rvalue) in statements {
        body.basic_blocks.as_mut()[block]
            .statements
            .push(mir::Statement::new(
                bounds_check.source_info,
                StatementKind::Assign(Box::new((local.into(), rvalue))),
            ));
    }
    Operand::Move(slice_ref.into())
}

/// Removes the MIR temporaries that only supported the now-replaced bounds check.
///
/// A temporary that is still read elsewhere is kept: with optimizations enabled, rustc reuses
/// a `len()` the program computes itself as the bounds check's length (`a[a.len() - 1]`).
fn remove_bounds_check_setup<'tcx>(body: &mut Body<'tcx>, bounds_check: &BoundsCheck<'tcx>) {
    // Ordered so that each local's readers among these come before it: the condition reads the
    // length, which reads the `PtrMetadata` operand.
    let mut lowered_locals: Vec<_> = bounds_check.condition_local.into_iter().collect();
    if let Some(len_place) = bounds_check
        .len
        .place()
        .filter(|place| place.projection.is_empty())
    {
        lowered_locals.push(len_place.local);
        for statement in &body.basic_blocks[bounds_check.block].statements {
            let Some((lhs, Rvalue::UnaryOp(mir::UnOp::PtrMetadata, operand))) =
                statement.kind.as_assign()
            else {
                continue;
            };
            if lhs.local == len_place.local {
                if let Some(raw_place) = operand.place().filter(|place| place.projection.is_empty())
                {
                    lowered_locals.push(raw_place.local);
                }
            }
        }
    }

    for local in lowered_locals {
        if is_read(body, local) {
            tracing::trace!(?local, "keeping bounds-check temporary that is still read");
            continue;
        }
        tracing::trace!(?local, "removing replaced bounds-check temporary");
        for statement in &mut body.basic_blocks.as_mut()[bounds_check.block].statements {
            if statement
                .kind
                .as_assign()
                .is_some_and(|(lhs, _)| lhs.local == local)
            {
                statement.kind = StatementKind::Nop;
            }
        }
    }
}

/// Whether any statement or terminator in `body` uses `local` other than by assigning to it.
fn is_read(body: &Body<'_>, local: Local) -> bool {
    use mir::visit::Visitor as _;

    let mut finder = ReadFinder {
        local,
        found: false,
    };
    for (block, data) in body.basic_blocks.iter_enumerated() {
        finder.visit_basic_block_data(block, data);
    }
    finder.found
}

fn lang_item_method(tcx: TyCtxt<'_>, item: LangItem, name: Symbol) -> DefId {
    let trait_id = tcx.lang_items().get(item).unwrap();
    tcx.associated_items(trait_id)
        .in_definition_order()
        .find(|item| item.name() == name && item.namespace() == Namespace::ValueNS)
        .unwrap()
        .def_id
}

#[cfg(test)]
mod tests;
