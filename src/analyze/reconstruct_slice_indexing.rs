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

/// The index of a bounds check as the indexed place projects it: a local (`[_2]`), or a
/// constant once constant propagation has replaced that local (`[2 of 3]`).
#[derive(Clone, Copy)]
enum IndexElem {
    Local(Local),
    Const(u64),
}

impl IndexElem {
    fn matches(self, elem: mir::PlaceElem<'_>) -> bool {
        match (self, elem) {
            (IndexElem::Local(local), mir::PlaceElem::Index(index)) => local == index,
            (
                IndexElem::Const(index),
                mir::PlaceElem::ConstantIndex {
                    offset,
                    from_end: false,
                    ..
                },
            ) => index == offset,
            _ => false,
        }
    }
}

/// The bounds-check block emitted for an indexing expression.
struct BoundsCheck<'tcx> {
    block: BasicBlock,
    condition_local: Option<Local>,
    /// The length the check compares with; `None` for an index constant propagation proved in
    /// bounds and left unchecked.
    len: Option<Operand<'tcx>>,
    index: Operand<'tcx>,
    index_elem: IndexElem,
    target: BasicBlock,
    unwind: mir::UnwindAction,
    source_info: mir::SourceInfo,
}

/// The slice access in the target of a [`BoundsCheck`].
struct SliceAccess<'tcx> {
    indexed_place: mir::Place<'tcx>,
    /// The first use of `indexed_place` in the target block.
    location: mir::Location,
    receiver: mir::Place<'tcx>,
    receiver_mutability: mir_ty::Mutability,
    /// The type of `receiver` when it is an array indexed in place (`array[index]`), which the
    /// call takes borrowed and unsized to a slice; `None` when `receiver` is a reference to a
    /// slice (`(*receiver)[index]`).
    array_ty: Option<Ty<'tcx>>,
    slice_ty: Ty<'tcx>,
    elem_ty: Ty<'tcx>,
    mutable: bool,
}

struct IndexedPlaceFinder<'a, 'tcx> {
    body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    index: IndexElem,
    found: Option<(mir::Place<'tcx>, bool, mir::Location)>,
}

impl<'tcx> mir::visit::Visitor<'tcx> for IndexedPlaceFinder<'_, 'tcx> {
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        context: mir::visit::PlaceContext,
        location: mir::Location,
    ) {
        if self.found.is_some() {
            return;
        }
        let Some(index_pos) = place
            .projection
            .iter()
            .position(|elem| self.index.matches(elem))
        else {
            return;
        };
        let indexed = mir::Place {
            local: place.local,
            projection: self
                .tcx
                .mk_place_elems(&place.projection.as_slice()[..=index_pos]),
        };
        let base = mir::Place {
            local: place.local,
            projection: self
                .tcx
                .mk_place_elems(&place.projection.as_slice()[..index_pos]),
        };
        if matches!(
            base.ty(&self.body.local_decls, self.tcx).ty.kind(),
            mir_ty::TyKind::Slice(_) | mir_ty::TyKind::Array(..)
        ) {
            self.found = Some((indexed, context.is_mutating_use(), location));
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
    for block in body.basic_blocks.indices().collect::<Vec<_>>() {
        let Some(bounds_check) = find_bounds_check(tcx, body, block) else {
            continue;
        };
        let Some(access) = find_slice_access(tcx, body, &bounds_check)
            .filter(|access| checks_length_of(tcx, body, &bounds_check, access))
        else {
            tracing::trace!(?block, "bounds check is not followed by slice indexing");
            continue;
        };
        // The rewritten target uses a result local defined by this block's new call. Entering it
        // from another predecessor would leave that local undefined.
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
        reconstruct_access(tcx, body, bounds_check, access);
    }
    while let Some((block, statement_index, offset)) = find_unchecked_array_index(tcx, body) {
        let bounds_check = split_at_unchecked_index(tcx, body, block, statement_index, offset);
        let access = find_slice_access(tcx, body, &bounds_check)
            .expect("an unchecked constant index of an array must be found again");
        tracing::debug!(
            ?block,
            target = ?bounds_check.target,
            indexed_place = ?access.indexed_place,
            mutable = access.mutable,
            "reconstructing a trait method call from unchecked array indexing"
        );
        reconstruct_access(tcx, body, bounds_check, access);
    }
}

/// Finds an array indexed at a constant without a bounds check, which constant propagation
/// leaves of `array[2]` (`_1[2 of 3]`) and an array pattern makes (`let [a, b] = array`), as the
/// block, the statement (the number of statements for the terminator) and the index. A move out
/// of the element is left as it is.
fn find_unchecked_array_index<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Option<(BasicBlock, usize, u64)> {
    use mir::visit::Visitor as _;

    struct Finder<'a, 'tcx> {
        body: &'a Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        found: Option<(mir::Location, u64)>,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for Finder<'_, 'tcx> {
        fn visit_place(
            &mut self,
            place: &mir::Place<'tcx>,
            context: mir::visit::PlaceContext,
            location: mir::Location,
        ) {
            use mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext};
            // A move out of an element (an array pattern binding a non-`Copy` element) or the
            // drop of one left behind is not an access through a reference.
            if self.found.is_some()
                || matches!(
                    context,
                    PlaceContext::NonMutatingUse(NonMutatingUseContext::Move)
                        | PlaceContext::MutatingUse(MutatingUseContext::Drop)
                )
            {
                return;
            }
            self.found = place
                .iter_projections()
                .find_map(|(base, elem)| match elem {
                    mir::PlaceElem::ConstantIndex {
                        offset,
                        from_end: false,
                        ..
                    } if base.ty(&self.body.local_decls, self.tcx).ty.is_array() => Some(offset),
                    _ => None,
                })
                .map(|offset| (location, offset));
        }
    }

    let mut finder = Finder {
        body,
        tcx,
        found: None,
    };
    for (block, data) in body.basic_blocks.iter_enumerated() {
        if !data.is_cleanup {
            finder.visit_basic_block_data(block, data);
        }
    }
    let (location, offset) = finder.found?;
    Some((location.block, location.statement_index, offset))
}

/// Splits `block` around its statement `statement_index` (its terminator when there are no more
/// statements), which indexes an array at the constant `offset` unchecked: the statements before
/// it stay in `block`, to end with the indexing call, and the access gets a block of its own, as
/// the call's target, so that the call stands for this access only. Returns them as the bounds
/// check the call replaces.
fn split_at_unchecked_index<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    block: BasicBlock,
    statement_index: usize,
    offset: u64,
) -> BoundsCheck<'tcx> {
    let blocks = body.basic_blocks.as_mut();
    let data = &mut blocks[block];
    let source_info = data.statements.get(statement_index).map_or_else(
        || data.terminator().source_info,
        |statement| statement.source_info,
    );
    let mut statements = data.statements.split_off(statement_index);
    let mut terminator = data.terminator.take();
    if statements.len() > 1 {
        let rest = statements.split_off(1);
        let rest = blocks.push(mir::BasicBlockData::new_stmts(rest, terminator, false));
        terminator = Some(mir::Terminator {
            source_info,
            kind: TerminatorKind::Goto { target: rest },
        });
    }
    let target = blocks.push(mir::BasicBlockData::new_stmts(
        statements, terminator, false,
    ));
    let index = Operand::Constant(Box::new(mir::ConstOperand {
        span: source_info.span,
        user_ty: None,
        const_: mir::Const::from_usize(tcx, offset),
    }));
    BoundsCheck {
        block,
        condition_local: None,
        len: None,
        index,
        index_elem: IndexElem::Const(offset),
        target,
        unwind: mir::UnwindAction::Continue,
        source_info,
    }
}

/// Recognizes the bounds-check terminator and records its index, a simple local or a constant.
fn find_bounds_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    block: BasicBlock,
) -> Option<BoundsCheck<'tcx>> {
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
    let index_elem = match index {
        Operand::Constant(constant) => {
            IndexElem::Const(constant.const_.try_to_scalar_int()?.to_target_usize(tcx))
        }
        _ => {
            let index_place = index.place()?;
            if !index_place.projection.is_empty() {
                return None;
            }
            IndexElem::Local(index_place.local)
        }
    };

    Some(BoundsCheck {
        block,
        condition_local: cond
            .place()
            .filter(|place| place.projection.is_empty())
            .map(|place| place.local),
        len: Some(len.clone()),
        index: index.clone(),
        index_elem,
        target: *target,
        unwind: *unwind,
        source_info: terminator.source_info,
    })
}

/// Whether the bounds check covers `access`, the first use of its index in its target block: for
/// an array indexed in place, the check compares with the constant `N` of the array's type; for a
/// slice, with a `PtrMetadata` of the access's reference computed next to the access
/// ([`adjacent_metadata`], how rustc lowers an indexing expression at opt-level 0), or of an
/// argument the body never writes ([`argument_metadata`]). With optimizations a check whose own
/// access is gone (`let _ = s[3];`) can be followed by another access at the same index whose
/// check was dropped, which it does not cover; any shape other than these is left to rustc's
/// check.
fn checks_length_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
    access: &SliceAccess<'tcx>,
) -> bool {
    let Some(len) = &bounds_check.len else {
        return true;
    };
    if let Some(array_ty) = access.array_ty {
        let mir_ty::TyKind::Array(_, array_len) = array_ty.kind() else {
            unreachable!("an array access of a non-array type");
        };
        let constant = len
            .constant()
            .and_then(|constant| constant.const_.try_to_scalar_int())
            .map(|int| int.to_target_usize(tcx));
        return constant.is_some() && constant == array_len.try_to_target_usize(tcx);
    }
    let Some(len) = len.place() else {
        return false;
    };
    adjacent_metadata(tcx, body, bounds_check, len, access)
        || argument_metadata(body, len, access.receiver)
}

/// Whether `len` is a `PtrMetadata` computed in the check block of the access's reference,
/// directly or through a copy or reborrow of it made in that block, and every statement from
/// there to the access writes, if anything, a local other than the reference's and the copy's.
fn adjacent_metadata<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
    len: mir::Place<'tcx>,
    access: &SliceAccess<'tcx>,
) -> bool {
    let receiver = access.receiver;
    let check_statements = &body.basic_blocks[bounds_check.block].statements;
    let assignment_in_check_block = |local: Local| {
        check_statements
            .iter()
            .enumerate()
            .find_map(|(index, statement)| {
                let (place, rvalue) = statement.kind.as_assign()?;
                (place.as_local() == Some(local)).then_some((index, rvalue))
            })
    };
    let Some((metadata, Rvalue::UnaryOp(mir::UnOp::PtrMetadata, reference))) =
        len.as_local().and_then(assignment_in_check_block)
    else {
        return false;
    };
    let Some(reference) = reference.place() else {
        return false;
    };
    let (start, copy) = if reference == receiver {
        (metadata, None)
    } else {
        let receiver_deref = tcx.mk_place_deref(receiver);
        let Some((copied_at, rvalue)) = reference.as_local().and_then(assignment_in_check_block)
        else {
            return false;
        };
        let copies = match rvalue {
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => *place == receiver,
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => *place == receiver_deref,
            _ => false,
        };
        if !copies || copied_at > metadata {
            return false;
        }
        (copied_at, reference.as_local())
    };
    let target_statements =
        &body.basic_blocks[access.location.block].statements[..access.location.statement_index];
    check_statements[start + 1..]
        .iter()
        .chain(target_statements)
        .all(|statement| match &statement.kind {
            StatementKind::Assign(assign) => assign
                .0
                .as_local()
                .is_some_and(|local| local != receiver.local && Some(local) != copy),
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::FakeRead(_)
            | StatementKind::Nop => true,
            _ => false,
        })
}

/// Whether `receiver` is an argument that the body never writes and `len` holds its
/// `PtrMetadata`, wherever that is computed: an argument never written holds its entry value at
/// every point, and a slice's length is part of the reference value. With optimizations rustc
/// reuses the length a guard computed (`if i < v.len() { v[i] = 7; }`).
fn argument_metadata<'tcx>(
    body: &Body<'tcx>,
    len: mir::Place<'tcx>,
    receiver: mir::Place<'tcx>,
) -> bool {
    let Some(argument) = receiver
        .as_local()
        .filter(|local| body.args_iter().any(|arg| arg == *local))
    else {
        return false;
    };
    let Some(len) = len.as_local() else {
        return false;
    };
    let len_writes = writes_of(body, len);
    let len_is_metadata = len_writes.len() == 1
        && len_writes.iter().all(|location| {
            body.stmt_at(*location).left().and_then(|statement| statement.kind.as_assign()).is_some_and(
                |(_, rvalue)| {
                    matches!(rvalue, Rvalue::UnaryOp(mir::UnOp::PtrMetadata, Operand::Copy(place) | Operand::Move(place)) if *place == receiver)
                },
            )
        });
    len_is_metadata && writes_of(body, argument).is_empty()
}

/// The locations in the whole body, statements and terminators, that write `local` or a part of
/// it not behind a pointer: assignments, call destinations, mutable borrows, drops and any other
/// mutating use.
fn writes_of(body: &Body<'_>, local: Local) -> Vec<mir::Location> {
    use mir::visit::Visitor as _;

    struct Writes {
        local: Local,
        locations: Vec<mir::Location>,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for Writes {
        fn visit_place(
            &mut self,
            place: &mir::Place<'tcx>,
            context: mir::visit::PlaceContext,
            location: mir::Location,
        ) {
            let through_pointer = place.projection.first() == Some(&mir::PlaceElem::Deref);
            if place.local == self.local && context.is_mutating_use() && !through_pointer {
                self.locations.push(location);
            }
        }
    }

    let mut writes = Writes {
        local,
        locations: Vec::new(),
    };
    writes.visit_body(body);
    writes.locations
}

/// Finds the matching `(*slice)[index]` place in the bounds check's target block.
fn find_slice_access<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
) -> Option<SliceAccess<'tcx>> {
    use mir::visit::Visitor as _;

    let mut finder = IndexedPlaceFinder {
        body,
        tcx,
        index: bounds_check.index_elem,
        found: None,
    };
    finder.visit_basic_block_data(bounds_check.target, &body.basic_blocks[bounds_check.target]);
    let (indexed_place, mutable, location) = finder.found?;

    // The indexed place has the shape `receiver.*[index]`, or `array[index]`; strip the index
    // and the dereference to recover the reference passed to `Index::index` or
    // `IndexMut::index_mut`, or the array it borrows.
    let mut receiver_projection = indexed_place.projection.as_slice().to_vec();
    if !receiver_projection
        .pop()
        .is_some_and(|elem| bounds_check.index_elem.matches(elem))
    {
        return None;
    }
    let array = mir::Place {
        local: indexed_place.local,
        projection: tcx.mk_place_elems(&receiver_projection),
    };
    let array_ty = array.ty(&body.local_decls, tcx).ty;
    if let mir_ty::TyKind::Array(elem_ty, _) = array_ty.kind() {
        return Some(SliceAccess {
            indexed_place,
            location,
            receiver: array,
            receiver_mutability: if mutable {
                mir_ty::Mutability::Mut
            } else {
                mir_ty::Mutability::Not
            },
            array_ty: Some(array_ty),
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
        location,
        receiver,
        receiver_mutability: *receiver_mutability,
        array_ty: None,
        slice_ty: *slice_ty,
        elem_ty: *elem_ty,
        mutable,
    })
}

fn reconstruct_access<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    bounds_check: BoundsCheck<'tcx>,
    access: SliceAccess<'tcx>,
) {
    let region = mir_ty::Region::new_from_kind(tcx, mir_ty::RegionKind::ReErased);
    let result_ty = mir_ty::Ty::new_ref(
        tcx,
        region,
        access.elem_ty,
        if access.mutable {
            mir_ty::Mutability::Mut
        } else {
            mir_ty::Mutability::Not
        },
    );
    let result_local = body
        .local_decls
        .push(mir::LocalDecl::new(result_ty, bounds_check.source_info.span).immutable());

    replace_indexed_place(
        body,
        tcx,
        bounds_check.target,
        access.indexed_place,
        result_local,
    );
    let receiver = receiver_operand(tcx, body, &bounds_check, &access, region);

    let (lang_item, method_name) = if access.mutable {
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

    body.basic_blocks.as_mut()[bounds_check.block].terminator = Some(mir::Terminator {
        source_info: bounds_check.source_info,
        kind: TerminatorKind::Call {
            func,
            args: call_args,
            destination: result_local.into(),
            target: Some(bounds_check.target),
            unwind: bounds_check.unwind,
            call_source: mir::CallSource::Normal,
            fn_span: bounds_check.source_info.span,
        },
    });
    tracing::trace!(?result_local, ?method, "slice indexing call inserted");
    remove_bounds_check_setup(body, &bounds_check);
}

/// Replaces every use of the indexed place in the target block with `*result_local`.
fn replace_indexed_place<'tcx>(
    body: &mut Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    target: BasicBlock,
    indexed_place: mir::Place<'tcx>,
    result_local: Local,
) {
    let replacement = tcx.mk_place_deref(result_local.into());
    let mut replacer =
        analyze::ReplacePlacesVisitor::with_replacement(tcx, indexed_place, replacement);
    let target_data = &mut body.basic_blocks.as_mut()[target];
    for statement in &mut target_data.statements {
        replacer.visit_statement(statement);
    }
    if let Some(terminator) = &mut target_data.terminator {
        replacer.visit_terminator(terminator);
    }
}

/// Builds the receiver operand, inserting a shared reborrow when indexing through `&mut [T]`.
fn receiver_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
    access: &SliceAccess<'tcx>,
    region: mir_ty::Region<'tcx>,
) -> Operand<'tcx> {
    if let Some(array_ty) = access.array_ty {
        return array_slice_ref(tcx, body, bounds_check, access, region, array_ty);
    }
    if !access.mutable && access.receiver_mutability.is_mut() {
        let ty = mir_ty::Ty::new_ref(tcx, region, access.slice_ty, mir_ty::Mutability::Not);
        let local = body
            .local_decls
            .push(mir::LocalDecl::new(ty, bounds_check.source_info.span).immutable());
        body.basic_blocks.as_mut()[bounds_check.block]
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
    } else if access.mutable {
        Operand::Move(access.receiver)
    } else {
        Operand::Copy(access.receiver)
    }
}

/// Borrows the array indexed in place and unsizes the borrow to the slice reference the call
/// takes, as rustc does for a slice method called on an array.
fn array_slice_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
    access: &SliceAccess<'tcx>,
    region: mir_ty::Region<'tcx>,
    array_ty: Ty<'tcx>,
) -> Operand<'tcx> {
    let mutability = access.receiver_mutability;
    let span = bounds_check.source_info.span;
    let array_ref_ty = Ty::new_ref(tcx, region, array_ty, mutability);
    let array_ref = body
        .local_decls
        .push(mir::LocalDecl::new(array_ref_ty, span).immutable());
    let slice_ref_ty = Ty::new_ref(tcx, region, access.slice_ty, mutability);
    let slice_ref = body
        .local_decls
        .push(mir::LocalDecl::new(slice_ref_ty, span).immutable());
    let borrow_kind = if mutability.is_mut() {
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
    let assigns = [
        (array_ref, Rvalue::Ref(region, borrow_kind, access.receiver)),
        (
            slice_ref,
            Rvalue::Cast(unsize, Operand::Move(array_ref.into()), slice_ref_ty),
        ),
    ];
    let statements = &mut body.basic_blocks.as_mut()[bounds_check.block].statements;
    for (local, rvalue) in assigns {
        statements.push(mir::Statement::new(
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
        .as_ref()
        .and_then(|len| len.place())
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
