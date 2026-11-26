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

/// What the receiver of a [`SliceAccess`] is, which says how the call gets a reference to the
/// slice from it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ReceiverKind {
    /// The reference to the slice, passed on.
    Reference,
    /// An array place, borrowed and unsized to a slice.
    Array,
    /// The slice a `Box<[T]>` holds (`*b`), borrowed, as Creusot reads a `Box<T>` as its content.
    BoxedSlice,
}

/// The slice access in the target of a [`BoundsCheck`].
struct SliceAccess<'tcx> {
    indexed_place: mir::Place<'tcx>,
    receiver: mir::Place<'tcx>,
    receiver_kind: ReceiverKind,
    receiver_mutability: mir_ty::Mutability,
    slice_ty: Ty<'tcx>,
    elem_ty: Ty<'tcx>,
    mutable: bool,
}

/// The statements and terminators that use the indexed place of a [`SliceAccess`], all reached
/// only through the bounds check.
struct AccessUses {
    locations: Vec<mir::Location>,
}

/// Finds the first `(*slice)[index]` place in the blocks it visits and every use of that place.
struct IndexedPlaceFinder<'a, 'tcx> {
    body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    index: Local,
    /// The slice the bounds check compares with, when known ([`checked_slice`]): a place that
    /// indexes another sequence is not the access the check guards.
    checked_slice: Option<mir::Place<'tcx>>,
    /// The constant length the bounds check compares with, an array's: a place that indexes a
    /// sequence of another type is not the access the check guards.
    checked_len: Option<u64>,
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
            if self.checked_slice.is_some_and(|slice| slice != base) {
                return;
            }
            if self
                .checked_len
                .is_some_and(|len| array_len(self.tcx, self.body, base) != Some(len))
            {
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
    let mut next = 0;
    while next < body.basic_blocks.len() {
        let block = BasicBlock::from_usize(next);
        next += 1;
        let Some(bounds_check) = find_bounds_check(body, block) else {
            continue;
        };
        let region = access_region(tcx, body, &bounds_check);
        let Some((access, uses)) = find_slice_access(tcx, body, &bounds_check, &region) else {
            tracing::trace!(?block, "bounds check is not followed by slice indexing");
            read_length_through_reference(tcx, body, &bounds_check);
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
        reconstruct_access(tcx, body, bounds_check, access, &uses);
    }
}

/// Reads the length a bounds check compares with from the reference to the sequence, as
/// `InstSimplify` does and Thrust reads MIR without it: `_raw = &raw const (fake) (*r)` and
/// `_len = PtrMetadata(move _raw)` become `_len = PtrMetadata(copy r)`. The access the check
/// guarded is gone (it is a read of a two-phase borrow's reserved place, redirected to the
/// borrow), so the check stays as it is.
fn read_length_through_reference<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
) {
    let block = bounds_check.block;
    let mut fake_raw_pointers = Vec::new();
    for statement in &body.basic_blocks[block].statements {
        let Some((lhs, Rvalue::RawPtr(mir::RawPtrKind::FakeForPtrMetadata, place))) =
            statement.kind.as_assign()
        else {
            continue;
        };
        let (Some(local), Some((&mir::PlaceElem::Deref, outer))) =
            (lhs.as_local(), place.projection.split_last())
        else {
            continue;
        };
        let reference = mir::Place {
            local: place.local,
            projection: tcx.mk_place_elems(outer),
        };
        fake_raw_pointers.push((local, reference));
    }
    for statement in body.basic_blocks.as_mut()[block].statements.iter_mut() {
        let StatementKind::Assign(assign) = &mut statement.kind else {
            continue;
        };
        let Rvalue::UnaryOp(mir::UnOp::PtrMetadata, operand) = &mut assign.1 else {
            continue;
        };
        let raw = operand.place().and_then(|place| place.as_local());
        if let Some((_, reference)) = fake_raw_pointers
            .iter()
            .find(|(local, _)| Some(*local) == raw)
        {
            *operand = Operand::Copy(*reference);
        }
    }
    for (local, _) in fake_raw_pointers {
        if is_read(body, local) {
            continue;
        }
        for statement in &mut body.basic_blocks.as_mut()[block].statements {
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
/// the same index that may check the same sequence, in depth-first order. The block that ends in
/// that check belongs to the region, for the statements before the check, but the blocks after it
/// are reached through the call that the check is reconstructed into. A check of the same index
/// against another slice, such as the inner one of `s[i][i]`, does not end the region, nor does
/// one against a constant length in the check's own target block, when that block does nothing
/// else ([`checks_only`]), such as the inner one of `a[i][i]` of `[[T; N]; M]`. A check further on
/// ends the region: a call or a branch in between can change the array, and the first check's
/// access must not read the array as it is after them.
fn access_region<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
) -> Vec<BasicBlock> {
    let checked = checked_slice(tcx, body, bounds_check);
    let ends_region = |block: BasicBlock| {
        let Some(check) = find_bounds_check(body, block) else {
            return false;
        };
        if check.index_local != bounds_check.index_local {
            return false;
        }
        let other_slice = checked.is_some_and(|checked| {
            checked_slice(tcx, body, &check).is_some_and(|slice| slice != checked)
        });
        let other_array = block == bounds_check.target
            && checked_len(tcx, &check).is_some()
            && checks_only(body, &check);
        !other_slice && !other_array
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
        if ends_region(block) {
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
        checked_slice: checked_slice(tcx, body, bounds_check),
        checked_len: checked_len(tcx, bounds_check),
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
            receiver_kind: ReceiverKind::Array,
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
    if receiver.ty(&body.local_decls, tcx).ty.is_box() {
        let slice_ty = base.ty(&body.local_decls, tcx).ty;
        let mir_ty::TyKind::Slice(elem_ty) = slice_ty.kind() else {
            return None;
        };
        return Some(SliceAccess {
            indexed_place,
            receiver: base,
            receiver_kind: ReceiverKind::BoxedSlice,
            receiver_mutability: mutability_of(mutable),
            slice_ty,
            elem_ty: *elem_ty,
            mutable,
        });
    }
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
        receiver_kind: ReceiverKind::Reference,
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

/// Replaces `from` with the dereference of `result` in the statements and terminators at
/// `locations`.
fn replace_place_at<'tcx>(
    body: &mut Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    locations: &[mir::Location],
    from: mir::Place<'tcx>,
    result: Local,
) {
    replace_place_with(
        body,
        tcx,
        locations,
        from,
        tcx.mk_place_deref(result.into()),
    );
}

/// Replaces `from` with `to` in the statements and terminators at `locations`.
fn replace_place_with<'tcx>(
    body: &mut Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    locations: &[mir::Location],
    from: mir::Place<'tcx>,
    to: mir::Place<'tcx>,
) {
    let mut replacer = analyze::ReplacePlacesVisitor::with_replacement(tcx, from, to);
    for location in locations {
        let data = &mut body.basic_blocks.as_mut()[location.block];
        match data.statements.get_mut(location.statement_index) {
            Some(statement) => replacer.visit_statement(statement),
            None => replacer.visit_terminator(data.terminator_mut()),
        }
    }
}

/// The constant length `check` compares its index with, an array's.
fn checked_len<'tcx>(tcx: TyCtxt<'tcx>, check: &BoundsCheck<'tcx>) -> Option<u64> {
    let len = check.len.constant()?.const_.try_to_scalar_int()?;
    Some(len.to_target_usize(tcx))
}

/// The length of `sequence` when it is an array of a known length.
fn array_len<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    sequence: mir::Place<'tcx>,
) -> Option<u64> {
    let mir_ty::TyKind::Array(_, len) = sequence.ty(&body.local_decls, tcx).ty.kind() else {
        return None;
    };
    len.try_to_target_usize(tcx)
}

/// Whether the block of `check` does nothing but compute the check's condition, so that the
/// check sees the state its block starts in. A bounds check against a constant length that follows
/// another one this way checks either the same sequence in the same state, which the first check
/// covers, or an element the first one's access reaches into (`a[i][i]`).
fn checks_only(body: &Body<'_>, check: &BoundsCheck<'_>) -> bool {
    body.basic_blocks[check.block]
        .statements
        .iter()
        .all(|statement| match &statement.kind {
            StatementKind::Assign(assign) => {
                Some(assign.0.local) == check.condition_local && assign.0.projection.is_empty()
            }
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {
                true
            }
            _ => false,
        })
}

/// The slice whose length `check` compares its index with, when that length is the `PtrMetadata`
/// of a pointer to the slice taken in the check's block.
fn checked_slice<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    check: &BoundsCheck<'tcx>,
) -> Option<mir::Place<'tcx>> {
    let len = check.len.place()?.as_local()?;
    let statements = &body.basic_blocks[check.block].statements;
    let assigned = |local: Local| {
        statements.iter().find_map(|statement| {
            let (lhs, rvalue) = statement.kind.as_assign()?;
            (lhs.as_local() == Some(local)).then_some(rvalue)
        })
    };
    let Some(Rvalue::UnaryOp(mir::UnOp::PtrMetadata, pointer)) = assigned(len) else {
        return None;
    };
    let pointer = pointer.place()?;
    let pointee = match pointer.as_local().and_then(assigned) {
        Some(Rvalue::RawPtr(_, place)) => *place,
        _ => tcx.mk_place_deref(pointer),
    };
    Some(pointee)
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
    match access.receiver_kind {
        ReceiverKind::Array => {
            return array_receiver_operand(tcx, body, bounds_check, access, mutable, block, region);
        }
        ReceiverKind::BoxedSlice => {
            return boxed_slice_receiver_operand(
                tcx,
                body,
                bounds_check,
                access,
                mutable,
                block,
                region,
            );
        }
        ReceiverKind::Reference => {}
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

/// Borrows the slice a `Box<[T]>` holds at the end of `block`, as `boxed[index]` does through
/// `Box`'s `Deref` and `[T]`'s `Index` impl.
fn boxed_slice_receiver_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
    access: &SliceAccess<'tcx>,
    mutable: bool,
    block: BasicBlock,
    region: mir_ty::Region<'tcx>,
) -> Operand<'tcx> {
    let span = bounds_check.source_info.span;
    let slice_ref_ty = Ty::new_ref(tcx, region, access.slice_ty, mutability_of(mutable));
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
    body.basic_blocks.as_mut()[block]
        .statements
        .push(mir::Statement::new(
            bounds_check.source_info,
            StatementKind::Assign(Box::new((
                slice_ref.into(),
                Rvalue::Ref(region, borrow_kind, access.receiver),
            ))),
        ));
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
