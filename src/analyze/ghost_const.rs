//! Const generic parameters as implicit parameters of a function.
//!
//! A function with a const parameter `N` takes it as one more argument after its own, of the
//! const's type: a ghost argument,
//! as the refinement parameters of Flux's functions are. The body reads that one variable at every
//! occurrence of `N` (so `N == N` holds), a contract may mention it, and a call passes the
//! const argument it is made with: a value, or the caller's own parameter of that name.
//!
//! Only a plain function or an inherent method has them, and the extern spec of one, which has
//! the ghost arguments of its target, in the target's order. A parameter of the spec stands for
//! the ghost argument its call of the target passes it as (`go::<A, B>()` in a spec generic over
//! `<B, A>`), whatever its own position. A trait method, an impl of a trait's method and a
//! closure keep every occurrence of `N` as any value of its type, since their types are tied to
//! the trait's or to the function they describe.

use rustc_hir::def::DefKind;
use rustc_index::IndexVec;
use rustc_middle::mir::visit::{MutVisitor, PlaceContext};
use rustc_middle::mir::{self, Body, Local, Location, Operand};
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::DefId;

use crate::analyze;

/// A const parameter taken as a ghost argument.
#[derive(Debug, Clone, Copy)]
pub struct GhostConst<'tcx> {
    /// The index among the generic parameters of the function of the const parameter this
    /// argument stands for, its parents' included; `None` for the argument of an extern spec's
    /// target that the spec's call fixes to a value, which no parameter of the spec names.
    pub param_index: Option<u32>,
    pub ty: mir_ty::Ty<'tcx>,
}

/// The ghost arguments of the function `def_id`, in the order of its generic parameters; empty
/// when it takes none. The extern spec of a local function takes those of its target, in its
/// order.
pub fn ghost_consts<'tcx>(ctx: &analyze::Analyzer<'tcx>, def_id: DefId) -> Vec<GhostConst<'tcx>> {
    let tcx = ctx.tcx();
    let Some(local_def_id) = def_id.as_local() else {
        return Vec::new();
    };
    if analyze::annot::has_thrust_attr(tcx, def_id, &analyze::annot::extern_spec_fn_path()) {
        let spec_body = tcx.optimized_mir(def_id);
        let (target, target_args) =
            analyze::local_def::extern_spec_fn_target_def_id_impl(&tcx, &local_def_id, spec_body);
        return ghost_consts(ctx, target)
            .into_iter()
            .map(|ghost| GhostConst {
                param_index: ghost.param_index.and_then(|index| {
                    const_param_index(target_args[index as usize].expect_const())
                }),
                ty: ghost.ty,
            })
            .collect();
    }
    if tcx.is_closure_like(def_id)
        || !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
    {
        return Vec::new();
    }
    if tcx.trait_of_assoc(def_id).is_some() || is_trait_impl_item(tcx, def_id) {
        return Vec::new();
    }
    const_params(tcx, def_id)
}

fn is_trait_impl_item(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.impl_of_assoc(def_id)
        .is_some_and(|impl_def_id| tcx.impl_trait_ref(impl_def_id).is_some())
}

fn const_params<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Vec<GhostConst<'tcx>> {
    let generics = tcx.generics_of(def_id);
    (0..generics.count())
        .filter_map(|idx| {
            let param = generics.param_at(idx, tcx);
            if !matches!(param.kind, mir_ty::GenericParamDefKind::Const { .. }) {
                return None;
            }
            Some(GhostConst {
                param_index: Some(idx as u32),
                ty: tcx.type_of(param.def_id).instantiate_identity(),
            })
        })
        .collect()
}

/// The index of the const parameter `ct` is, if it is one.
fn const_param_index(ct: mir_ty::Const<'_>) -> Option<u32> {
    match ct.kind() {
        mir_ty::ConstKind::Param(param) => Some(param.index),
        mir_ty::ConstKind::Infer(_)
        | mir_ty::ConstKind::Bound(..)
        | mir_ty::ConstKind::Placeholder(_)
        | mir_ty::ConstKind::Unevaluated(_)
        | mir_ty::ConstKind::Value(_)
        | mir_ty::ConstKind::Error(_)
        | mir_ty::ConstKind::Expr(_) => None,
    }
}

fn operand_const_param(operand: &Operand<'_>) -> Option<u32> {
    let Operand::Constant(constant) = operand else {
        return None;
    };
    match constant.const_ {
        mir::Const::Ty(_, ct) => const_param_index(ct),
        mir::Const::Unevaluated(..) | mir::Const::Val(..) => None,
    }
}

/// The local that holds the ghost argument for the const parameter `param_index` of `def_id` in
/// its body, if it takes one.
pub fn ghost_local<'tcx>(
    ctx: &analyze::Analyzer<'tcx>,
    def_id: DefId,
    param_index: u32,
) -> Option<Local> {
    let ghosts = ghost_consts(ctx, def_id);
    let position = ghosts
        .iter()
        .position(|g| g.param_index == Some(param_index))?;
    Some(ghost_local_at(ctx.tcx(), def_id, position))
}

/// The local of the `position`th ghost argument of `def_id`: after the arguments the source
/// declares.
fn ghost_local_at(tcx: TyCtxt<'_>, def_id: DefId, position: usize) -> Local {
    Local::from_usize(tcx.optimized_mir(def_id).arg_count + 1 + position)
}

/// Appends the ghost arguments to the arguments of `body`, which is the body of `def_id`, and
/// makes each read of a const parameter a read of its argument.
pub fn add_ghost_args<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>, ghosts: &[GhostConst<'tcx>]) {
    let first = body.arg_count + 1;
    let count = ghosts.len();
    let span = body.span;
    let (args, temps) = body.local_decls.raw.split_at(first);
    let ghost_decls = ghosts
        .iter()
        .map(|ghost| mir::LocalDecl::new(ghost.ty, span));
    let decls: Vec<_> = args
        .iter()
        .cloned()
        .chain(ghost_decls)
        .chain(temps.iter().cloned())
        .collect();
    let decls = IndexVec::from_raw(decls);
    body.local_decls = decls;
    body.arg_count += count;
    if let Some(spread) = body.spread_arg {
        body.spread_arg = Some(shift(first, count, spread));
    }
    let mut rewrite = Rewrite { tcx, first, ghosts };
    rewrite.visit_body(body);
}

fn shift(first: usize, count: usize, local: Local) -> Local {
    if local.as_usize() < first {
        local
    } else {
        Local::from_usize(local.as_usize() + count)
    }
}

struct Rewrite<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    first: usize,
    ghosts: &'a [GhostConst<'tcx>],
}

impl<'tcx> MutVisitor<'tcx> for Rewrite<'_, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_local(&mut self, local: &mut Local, _: PlaceContext, _: Location) {
        *local = shift(self.first, self.ghosts.len(), *local);
    }

    fn visit_operand(&mut self, operand: &mut Operand<'tcx>, location: Location) {
        let ghost = operand_const_param(operand).and_then(|index| {
            self.ghosts
                .iter()
                .position(|g| g.param_index == Some(index))
        });
        if let Some(position) = ghost {
            *operand = Operand::Copy(mir::Place::from(Local::from_usize(self.first + position)));
            return;
        }
        self.super_operand(operand, location);
    }
}
