//! The block of `block_contract_inline!`, which runs in place and is verified as a call of the
//! function it is extracted into.
//!
//! The macro leaves the body between two marker calls that name the extracted function `__bc`
//! (`__block_region_open_marker(__bc)`, `__block_region_close_marker(__bc)`). `__bc` takes the
//! outer variables of the block as parameters with their own types and has its own contract, so
//! the analysis reads the region as the call
//! `(result, x1, ..) = __bc(v1, .., x1, ..)` and never reads the body, which `__bc` verifies as
//! its own function. A parameter written `mut` is changed by the body, so `__bc` returns its
//! final value after the result and the call assigns it back to the outer variable; every other
//! variable keeps its value and facts, and a `&mut` parameter is passed as the call passes any
//! `&mut`, which gives the callee a fresh current value and keeps the final one.
//!
//! The rewrite is on the MIR, so that the call is typed as any other call to a function with a
//! contract is: the opening marker call becomes the call of `__bc`, followed by the assignments of
//! the results, and the blocks of the body are emptied.

use std::collections::{HashMap, HashSet};

use rustc_abi::FieldIdx;
use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::{self, BasicBlock, Body, Local, Location, Operand, Place, TerminatorKind};
use rustc_middle::ty::{self as mir_ty, TyCtxt};

use crate::analyze;
use crate::analyze::block_contract::{region_under, Region, RegionMarkers};

/// The name of the local that holds the value of the block's body, which the macro declares
/// before the closing marker.
const RESULT_NAME: &str = "__block_contract_result";

/// What to write instead of an exit that leaves the block.
const LEAVE_HINT: &str = ". To exit the function, return a `Result` as the block's value and apply \
     `?` after the block (for `return` and `?`); to exit a loop, return a `ControlFlow` and `match` \
     on it, or use `let ... else`, after the block (for `break` and `continue`)";

#[derive(Clone, Copy, PartialEq, Eq)]
enum RegionMarker {
    Open,
    Close,
}

/// The kind of region marker a block ends in and the extracted function the marker names.
fn marker_at<'tcx>(
    ctx: &analyze::Analyzer<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
) -> Option<(RegionMarker, mir_ty::Ty<'tcx>)> {
    let TerminatorKind::Call { func, args, .. } = &body.basic_blocks[bb].terminator().kind else {
        return None;
    };
    let (def_id, _) = func.const_fn_def()?;
    let marker = if Some(def_id) == ctx.def_ids().block_region_open_marker() {
        RegionMarker::Open
    } else if Some(def_id) == ctx.def_ids().block_region_close_marker() {
        RegionMarker::Close
    } else {
        return None;
    };
    Some((marker, args[0].node.ty(&body.local_decls, ctx.tcx())))
}

/// Replaces each region of `body` by the call of the function it is extracted into.
pub fn replace_regions_by_calls<'tcx>(ctx: &analyze::Analyzer<'tcx>, body: &mut Body<'tcx>) {
    let is = |body: &Body<'tcx>, bb: BasicBlock, wanted: RegionMarker| {
        marker_at(ctx, body, bb).is_some_and(|(marker, _)| marker == wanted)
    };
    let openings: Vec<BasicBlock> = body
        .basic_blocks
        .indices()
        .filter(|&bb| !body.basic_blocks[bb].is_cleanup && is(body, bb, RegionMarker::Open))
        .collect();
    for opening in openings {
        let region = region_under(
            ctx,
            body,
            opening,
            &RegionMarkers {
                open: "`block_contract_inline!`",
                close: "`block_contract_inline!` end marker",
                leave_hint: LEAVE_HINT,
                is_open: &|bb| is(body, bb, RegionMarker::Open),
                is_close: &|bb| is(body, bb, RegionMarker::Close),
            },
        );
        replace_region(ctx, body, opening, region);
    }
}

/// Whether the parameter of `bc` at `index` is written `mut`.
fn is_mut_param(tcx: TyCtxt<'_>, bc: rustc_hir::def_id::LocalDefId, index: usize) -> bool {
    let params = tcx.hir_body_owned_by(bc).params;
    matches!(
        params[index].pat.kind,
        rustc_hir::PatKind::Binding(rustc_hir::BindingMode(_, rustc_hir::Mutability::Mut), ..)
    )
}

/// The names of the parameters of the extracted function `bc`.
fn param_names(
    tcx: TyCtxt<'_>,
    bc: rustc_hir::def_id::LocalDefId,
) -> Vec<rustc_span::symbol::Ident> {
    tcx.hir_body_owned_by(bc)
        .params
        .iter()
        .map(|param| match param.pat.kind {
            rustc_hir::PatKind::Binding(_, _, ident, None) => ident,
            _ => panic!("a parameter of an extracted block is a name"),
        })
        .collect()
}

/// The places the name `name` is bound to at `scope`, and whether it is bound to a constant
/// (a unit value has no local).
fn bound_places<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    name: rustc_span::symbol::Ident,
    scope: mir::SourceScope,
) -> (Vec<Place<'tcx>>, bool) {
    let bound = analyze::basic_block::bindings_in_scope(tcx, body, name, scope);
    let places = bound
        .iter()
        .filter_map(|vdi| match vdi.value {
            mir::VarDebugInfoContents::Place(place) => Some(place),
            mir::VarDebugInfoContents::Const(_) => None,
        })
        .collect();
    let constant = bound
        .iter()
        .any(|vdi| matches!(vdi.value, mir::VarDebugInfoContents::Const(_)));
    (places, constant)
}

/// The place of the one local the name `name` is bound to at `scope`.
fn outer_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    name: rustc_span::symbol::Ident,
    scope: mir::SourceScope,
    span: rustc_span::Span,
) -> Place<'tcx> {
    match bound_places(tcx, body, name, scope).0.as_slice() {
        [place] => *place,
        _ => tcx.dcx().span_fatal(
            span,
            format!("`block_contract_inline!` parameter `{name}` names no single outer variable"),
        ),
    }
}

/// `ty` as a comparison of the types of a variable and of a parameter sees it: regions erased and
/// associated types normalized.
fn comparable_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> mir_ty::Ty<'tcx> {
    tcx.try_normalize_erasing_regions(typing_env, ty)
        .unwrap_or_else(|_| tcx.erase_regions(ty))
}

/// Whether a value of `ty`, passed as a parameter, holds a `&mut` the call does not reborrow: one
/// inside the value, or inside what a `&mut` parameter points to. Only a parameter that is a
/// `&mut` itself is reborrowed, so that the callee gets a fresh current value and the caller keeps
/// the final one; a `&mut` deeper in the type is copied, and a write through the copy would leave
/// the caller's value stale. A type parameter holds none here: a body cannot write through a value
/// of a type it does not know, and an instance that does hold one is rejected where the analysis
/// sees its type.
fn holds_unreborrowed_mut_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> bool {
    let inspected = match (ty.ref_mutability(), ty.builtin_deref(false)) {
        (Some(mir::Mutability::Mut), Some(pointee)) => pointee,
        _ => ty,
    };
    analyze::may_hold_mut_ref(tcx, typing_env, inspected)
}

/// Rejects a block whose parameters or result do not have exactly the types of the variables the
/// call passes, which the dead call in the macro's expansion lets through when a coercion
/// (`&mut T` to `&T`, `&&T` to `&T`, an unsizing) or an inference choice makes them agree, and a
/// non-`mut` parameter that holds a `&mut` below its top level.
fn check_parameter_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    body: &Body<'tcx>,
    sig: mir_ty::FnSig<'tcx>,
    names: &[rustc_span::symbol::Ident],
    params: &[(Place<'tcx>, bool)],
    span: rustc_span::Span,
) {
    for ((name, (place, is_mut)), declared) in names.iter().zip(params).zip(sig.inputs()) {
        let actual = place.ty(&body.local_decls, tcx).ty;
        if comparable_type(tcx, typing_env, actual) != comparable_type(tcx, typing_env, *declared) {
            tcx.dcx().span_fatal(
                span,
                format!(
                    "`block_contract_inline!` parameter `{name}` is declared `{declared}` but the \
                     variable has type `{actual}`; a parameter has exactly the type of the \
                     variable it names (no coercion)"
                ),
            );
        }
        if !is_mut && holds_unreborrowed_mut_ref(tcx, typing_env, actual) {
            tcx.dcx().span_fatal(
                span,
                format!(
                    "`block_contract_inline!` parameter `{name}` of type `{actual}` is not `mut` \
                     but holds a `&mut` inside the value; only a parameter that is itself a \
                     `&mut` is passed as a reborrow, so a write through the inner `&mut` would \
                     not reach the variable. Pass the inner `&mut` itself as a parameter"
                ),
            );
        }
    }
}

fn replace_region<'tcx>(
    ctx: &analyze::Analyzer<'tcx>,
    body: &mut Body<'tcx>,
    opening: BasicBlock,
    region: Region,
) {
    let tcx = ctx.tcx();
    let Region {
        closing,
        blocks,
        exit,
        ..
    } = region;
    let terminator = body.basic_blocks[opening].terminator().clone();
    let source_info = terminator.source_info;
    let TerminatorKind::Call {
        unwind, fn_span, ..
    } = terminator.kind
    else {
        unreachable!("a marker call returns");
    };
    let (_, bc_ty) = marker_at(ctx, body, opening).expect("an opening block ends in the marker");
    let mir_ty::TyKind::FnDef(bc, bc_args) = bc_ty.kind() else {
        panic!("a region marker names the extracted function");
    };
    let bc_local = bc.expect_local();
    let (_, closing_ty) =
        marker_at(ctx, body, closing).expect("a closing block ends in the marker");
    assert_eq!(
        bc_ty, closing_ty,
        "both markers of a region name one function"
    );

    let sig = tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(bc).instantiate(tcx, bc_args));
    let names = param_names(tcx, bc_local);
    let scope = source_info.scope;
    let params: Vec<(Place<'tcx>, bool)> = names
        .iter()
        .enumerate()
        .map(|(index, name)| {
            let place = outer_place(tcx, body, *name, scope, source_info.span);
            (place, is_mut_param(tcx, bc_local, index))
        })
        .collect();
    let args = params
        .iter()
        .map(|(place, _)| rustc_span::source_map::Spanned {
            node: Operand::Copy(*place),
            span: source_info.span,
        })
        .collect();

    let result_name = rustc_span::symbol::Ident::from_str(RESULT_NAME);
    let closing_info = body.basic_blocks[closing].terminator().source_info;
    let returned = sig.output();
    let in_out = params.iter().any(|(_, is_mut)| *is_mut);
    let result_ty = if in_out {
        returned.tuple_fields()[0]
    } else {
        returned
    };
    // MIR optimizations may give the value the local of an outer variable the body returns
    // (`{ x }`): the value is then that variable, which the call must not assign, so a fresh
    // local takes the call's result.
    let is_outer_variable = |place: &Place<'tcx>| params.iter().any(|(outer, _)| outer == place);
    let result_place = match bound_places(tcx, body, result_name, closing_info.scope) {
        (places, _) if places.len() == 1 && !is_outer_variable(&places[0]) => places[0],
        (places, _) if places.len() == 1 => body
            .local_decls
            .push(mir::LocalDecl::new(result_ty, closing_info.span).immutable())
            .into(),
        (places, true) if places.is_empty() => body
            .local_decls
            .push(mir::LocalDecl::new(result_ty, closing_info.span).immutable())
            .into(),
        _ => tcx.dcx().span_fatal(
            closing_info.span,
            "the value of a `block_contract_inline!` block names no single variable",
        ),
    };
    let typing_env = mir_ty::TypingEnv::post_analysis(tcx, body.source.def_id());
    check_parameter_types(
        tcx,
        typing_env,
        body,
        sig,
        &names,
        &params,
        source_info.span,
    );
    let result_actual = result_place.ty(&body.local_decls, tcx).ty;
    if comparable_type(tcx, typing_env, result_actual)
        != comparable_type(tcx, typing_env, result_ty)
    {
        tcx.dcx().span_fatal(
            closing_info.span,
            format!(
                "the value of a `block_contract_inline!` block has type `{result_actual}` but \
                 the block declares `{result_ty}`"
            ),
        );
    }
    let mut assignments = Vec::new();
    let mut destination = result_place;
    if in_out {
        let tmp = body
            .local_decls
            .push(mir::LocalDecl::new(returned, source_info.span).immutable());
        destination = tmp.into();
        let mut assign = |to: Place<'tcx>, index: usize, ty: mir_ty::Ty<'tcx>| {
            let field = tcx.mk_place_field(Place::from(tmp), FieldIdx::from_usize(index), ty);
            assignments.push(mir::Statement::new(
                source_info,
                mir::StatementKind::Assign(Box::new((to, mir::Rvalue::Use(Operand::Move(field))))),
            ));
        };
        let fields = returned.tuple_fields();
        assign(result_place, 0, fields[0]);
        let mut next = 1;
        for (place, is_mut) in &params {
            if *is_mut {
                assign(*place, next, fields[next]);
                next += 1;
            }
        }
    }

    let after_call = body.basic_blocks_mut().push(mir::BasicBlockData::new(
        Some(mir::Terminator {
            source_info,
            kind: TerminatorKind::Goto { target: exit },
        }),
        false,
    ));
    body.basic_blocks_mut()[after_call].statements = assignments;
    body.basic_blocks_mut()[opening].terminator_mut().kind = TerminatorKind::Call {
        func: Operand::function_handle(tcx, *bc, bc_args.iter(), source_info.span),
        args,
        destination,
        target: Some(after_call),
        unwind,
        call_source: mir::CallSource::Normal,
        fn_span,
    };
    for bb in blocks {
        let data = &mut body.basic_blocks_mut()[bb];
        data.statements.clear();
        data.terminator_mut().kind = TerminatorKind::Unreachable;
    }
}

/// Reports each use, in the body of a `block_contract_inline!` block, of a variable declared
/// outside the block that is not a parameter of the block. The block is verified as the function
/// `__bc`, which does not see such a variable: a name the body writes for it could resolve to a
/// module item there (a variable holding a closure or a function pointer shadows a function of
/// the module in place only).
///
/// This reads the MIR as borrowck does (`mir_promoted`), before the optimizations that rename one
/// local into another (`CopyProp` turns an unlisted `let y = x;` into a use of `x`), where a use
/// is an operand of a statement or terminator, a closure's captures included.
///
/// A function's check covers the closures written in it, whose borrowck rustc does with the
/// function's.
pub fn check_regions_use_only_parameters(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::LocalDefId) {
    let mut hoisted = check_body_regions(tcx, def_id);
    if tcx.typeck_root_def_id(def_id.to_def_id()) == def_id.to_def_id() {
        for nested in tcx.nested_bodies_within(def_id) {
            hoisted |= check_body_regions(tcx, nested);
        }
        if hoisted {
            check_host_has_no_items(tcx, def_id);
        }
    }
}

/// Reports an item statement (a nested `fn`, `const`, `static`, `use`, `struct`, `enum`, `trait`,
/// `impl`, `mod`, `macro_rules!`, whatever a macro expanded to) in the body of `host`, which
/// holds a block hoisted next to it. The hoisted function does not see the host's local items, so
/// a name the block writes could mean another item there. This reads the expanded HIR, which
/// sees the items macros declare; the macro `#[context]` rejects them before expansion too, for
/// an earlier message.
fn check_host_has_no_items(tcx: TyCtxt<'_>, host: rustc_hir::def_id::LocalDefId) {
    struct Items<'tcx> {
        tcx: TyCtxt<'tcx>,
        spans: Vec<rustc_span::Span>,
    }
    impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for Items<'tcx> {
        type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

        fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
            self.tcx
        }

        fn visit_stmt(&mut self, stmt: &'tcx rustc_hir::Stmt<'tcx>) {
            if let rustc_hir::StmtKind::Item(id) = stmt.kind {
                let span = self.tcx.hir_item(id).span;
                if !is_expanded_by_thrust_macros(self.tcx, span) {
                    self.spans.push(span);
                }
            }
            rustc_hir::intravisit::walk_stmt(self, stmt);
        }
    }
    let mut items = Items {
        tcx,
        spans: Vec::new(),
    };
    rustc_hir::intravisit::Visitor::visit_body(&mut items, tcx.hir_body_owned_by(host));
    for span in items.spans {
        tcx.dcx().span_err(
            span,
            "a function with a `block_contract_inline!` block has an item statement (a nested \
             `fn`, `const`, `static`, `use`, `struct`, `enum`, `trait`, `impl`, `mod` or \
             `macro_rules!`, also one a macro expands to): the block is verified as a function \
             next to its host, which does not see local items, so a name could mean another item \
             there. Move the item out of the function",
        );
    }
}

/// Whether `span` is code a macro of `thrust_macros` generated (the formula functions and the
/// context stub the spec macros leave in a function body), which no name of the user's can reach.
fn is_expanded_by_thrust_macros(tcx: TyCtxt<'_>, span: rustc_span::Span) -> bool {
    span.ctxt()
        .outer_expn_data()
        .macro_def_id
        .is_some_and(|macro_def| tcx.crate_name(macro_def.krate).as_str() == "thrust_macros")
}

/// Checks the blocks of the body of `def_id`, and whether one is hoisted next to a host, as a
/// function that is not nested in the body is.
fn check_body_regions(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::LocalDefId) -> bool {
    let (promoted, _) = tcx.mir_promoted(def_id);
    let body = promoted.borrow();
    let root = tcx.typeck_root_def_id(def_id.to_def_id());
    let mut hoisted = false;
    for bb in body.basic_blocks.indices() {
        if body.basic_blocks[bb].is_cleanup {
            continue;
        }
        if let Some(bc_ty) = marker_callee(tcx, &body, bb, "__block_region_open_marker") {
            check_region_uses(tcx, &body, bb, bc_ty);
            if let mir_ty::TyKind::FnDef(bc, _) = bc_ty.kind() {
                hoisted |= tcx.opt_parent(*bc) != Some(root);
            }
        }
    }
    hoisted
}

/// The extracted function's type the block ending in a call of the marker `name` passes to it.
fn marker_callee<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    name: &str,
) -> Option<mir_ty::Ty<'tcx>> {
    let TerminatorKind::Call { func, args, .. } = &body.basic_blocks[bb].terminator().kind else {
        return None;
    };
    let (def_id, _) = func.const_fn_def()?;
    if tcx.item_name(def_id).as_str() != name {
        return None;
    }
    Some(args[0].node.ty(&body.local_decls, tcx))
}

/// What a use of a place names: its local, and for the environment of a closure (`_1`) the
/// captured variable the place reaches, the first field below it, as `var_debug_info` names the
/// captures (`(*_1).0`).
type UseKey = (Local, Option<FieldIdx>);

fn use_key(is_closure: bool, local: Local, projection: &[mir::PlaceElem<'_>]) -> UseKey {
    if !is_closure || local != Local::from_u32(1) {
        return (local, None);
    }
    let capture = projection.iter().find_map(|elem| match elem {
        mir::PlaceElem::Field(field, _) => Some(*field),
        mir::PlaceElem::Deref
        | mir::PlaceElem::Index(_)
        | mir::PlaceElem::ConstantIndex { .. }
        | mir::PlaceElem::Subslice { .. }
        | mir::PlaceElem::Downcast(..)
        | mir::PlaceElem::OpaqueCast(_)
        | mir::PlaceElem::Subtype(_)
        | mir::PlaceElem::UnwrapUnsafeBinder(_) => None,
    });
    (local, capture)
}

/// What the code of a region uses, with where, and the locals it declares itself.
struct RegionLocals<'a, 'tcx> {
    body: &'a Body<'tcx>,
    is_closure: bool,
    declared: HashSet<Local>,
    used: Vec<(UseKey, rustc_span::Span)>,
}

impl<'tcx> Visitor<'tcx> for RegionLocals<'_, 'tcx> {
    fn visit_statement(&mut self, statement: &mir::Statement<'tcx>, location: Location) {
        if let mir::StatementKind::StorageLive(local) = statement.kind {
            self.declared.insert(local);
        }
        self.super_statement(statement, location);
    }

    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if context.is_storage_marker() {
            return;
        }
        let span = self.body.source_info(location).span;
        self.used.push((
            use_key(self.is_closure, place.local, place.projection),
            span,
        ));
        for elem in place.projection {
            if let mir::PlaceElem::Index(index) = elem {
                self.used.push(((index, None), span));
            }
        }
    }
}

fn check_region_uses<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    opening: BasicBlock,
    bc_ty: mir_ty::Ty<'tcx>,
) {
    let mir_ty::TyKind::FnDef(bc, _) = bc_ty.kind() else {
        return;
    };
    let Some(bc_local) = bc.as_local() else {
        return;
    };
    let is_closure = tcx.is_closure_like(body.source.def_id());
    let scope = body.basic_blocks[opening].terminator().source_info.scope;
    let listed: HashSet<UseKey> = param_names(tcx, bc_local)
        .into_iter()
        .flat_map(|name| bound_places(tcx, body, name, scope).0)
        .map(|place| use_key(is_closure, place.local, place.projection))
        .collect();

    let TerminatorKind::Call {
        target: Some(entry),
        ..
    } = body.basic_blocks[opening].terminator().kind
    else {
        return;
    };
    let mut locals = RegionLocals {
        body,
        is_closure,
        declared: HashSet::new(),
        used: Vec::new(),
    };
    let mut seen = HashSet::new();
    let mut stack = vec![entry];
    while let Some(bb) = stack.pop() {
        let data = &body.basic_blocks[bb];
        if data.is_cleanup || !seen.insert(bb) {
            continue;
        }
        locals.visit_basic_block_data(bb, data);
        let ends_region =
            marker_callee(tcx, body, bb, "__block_region_close_marker") == Some(bc_ty);
        if !ends_region {
            stack.extend(data.terminator().successors());
        }
    }

    // a temporary of the host has no name and is not an outer variable the body writes
    let names: HashMap<UseKey, rustc_span::symbol::Symbol> = body
        .var_debug_info
        .iter()
        .filter_map(|vdi| match vdi.value {
            mir::VarDebugInfoContents::Place(place) => {
                Some((use_key(is_closure, place.local, place.projection), vdi.name))
            }
            mir::VarDebugInfoContents::Const(_) => None,
        })
        .collect();
    let mut reported = HashSet::new();
    for (key, span) in &locals.used {
        let Some(name) = names.get(key) else {
            continue;
        };
        let is_outer = !locals.declared.contains(&key.0) && !listed.contains(key);
        if is_outer && reported.insert(*key) {
            tcx.dcx().span_err(
                *span,
                format!(
                    "the body of `block_contract_inline!` uses the variable `{name}`, which is \
                     declared outside the block and is not one of its parameters; the block is \
                     verified as a function that does not see it, where the name could mean \
                     another item. List `{name}` as a parameter"
                ),
            );
        }
    }
}
