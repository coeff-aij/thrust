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

use rustc_abi::FieldIdx;
use rustc_middle::mir::{self, BasicBlock, Body, Operand, Place, TerminatorKind};
use rustc_middle::ty::{self as mir_ty, TyCtxt};

use crate::analyze;
use crate::analyze::block_contract::{region_under, Region, RegionMarkers};

/// The name of the local that holds the value of the block's body, which the macro declares
/// before the closing marker.
const RESULT_NAME: &str = "__block_contract_result";

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
    let result_place = match bound_places(tcx, body, result_name, closing_info.scope) {
        (places, _) if places.len() == 1 => places[0],
        (places, true) if places.is_empty() => body
            .local_decls
            .push(mir::LocalDecl::new(result_ty, closing_info.span).immutable())
            .into(),
        _ => tcx.dcx().span_fatal(
            closing_info.span,
            "the value of a `block_contract_inline!` block names no single variable",
        ),
    };
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
