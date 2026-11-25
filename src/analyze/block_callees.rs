//! Checks that the calls of a `block_contract!` body mean the same in the host and in the
//! extracted function.
//!
//! The body runs in place, where the types of the outer variables are concrete, and is verified
//! as the extracted function `__bc`, where a type parameter stands for them. Method resolution
//! can pick another method in the two (a blanket impl against an inherent method of the same name,
//! a bound's method against an inherent one), so the block would be verified as a call that does
//! not run. This compares, for every call of the body, the method rustc's resolver picks in the
//! host with the one it picks in `__bc` instantiated with the host's arguments. The body's tokens
//! are shared, so a call is matched by its source span.

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::mir::{self, BasicBlock, Body, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::{
    self as mir_ty, GenericArgsRef, TyCtxt, TypeFoldable, TypeFolder, TypeSuperFoldable,
};
use rustc_span::Span;

/// What rustc resolves a call to: the method an instance runs, or, where the types are not known
/// enough to resolve (a type parameter of the host), the function and arguments as written.
#[derive(Clone, PartialEq, Eq)]
enum Callee<'tcx> {
    Method(
        std::mem::Discriminant<mir_ty::InstanceKind<'tcx>>,
        DefId,
        GenericArgsRef<'tcx>,
    ),
    /// A closure of the body; the host's and the extracted function's closures are different
    /// items, so only the kind of call is compared.
    Closure(std::mem::Discriminant<mir_ty::InstanceKind<'tcx>>),
    Unresolved(DefId, GenericArgsRef<'tcx>),
}

/// Where a call is written: the source span of its outermost macro call, which the body's
/// copies in the host and in the extracted function share. A span of a macro's expansion is not
/// equal across two expansions of the same call.
type CallPlace = (rustc_span::BytePos, rustc_span::BytePos);

fn call_place(span: Span) -> CallPlace {
    let written = span.source_callsite();
    (written.lo(), written.hi())
}

/// Replaces the closure types a predicate selects by one type, so that the closures of the body's
/// two copies, which are different items, compare equal where they stand in a callee's arguments.
struct ClosureEraser<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    is_body_closure: &'a dyn Fn(DefId) -> bool,
}

impl<'tcx> TypeFolder<mir_ty::TyCtxt<'tcx>> for ClosureEraser<'_, 'tcx> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_ty(&mut self, ty: mir_ty::Ty<'tcx>) -> mir_ty::Ty<'tcx> {
        if let mir_ty::TyKind::Closure(def_id, _) = ty.kind() {
            if (self.is_body_closure)(*def_id) {
                return self.tcx.types.unit;
            }
        }
        ty.super_fold_with(self)
    }
}

impl<'tcx> Callee<'tcx> {
    /// The callee with the closure types of the body, selected by `is_body_closure`, erased.
    fn without_body_closures(
        self,
        tcx: TyCtxt<'tcx>,
        is_body_closure: &dyn Fn(DefId) -> bool,
    ) -> Self {
        let mut eraser = ClosureEraser {
            tcx,
            is_body_closure,
        };
        match self {
            Callee::Method(kind, def_id, args) => {
                Callee::Method(kind, def_id, args.fold_with(&mut eraser))
            }
            Callee::Unresolved(def_id, args) => {
                Callee::Unresolved(def_id, args.fold_with(&mut eraser))
            }
            Callee::Closure(kind) => Callee::Closure(kind),
        }
    }
}

struct Call<'tcx> {
    span: Span,
    callee: Callee<'tcx>,
    /// The function as the host or the extracted function names it, for the message.
    written: DefId,
}

fn resolve<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    def_id: DefId,
    args: GenericArgsRef<'tcx>,
) -> Callee<'tcx> {
    let args = tcx.erase_regions(args);
    match mir_ty::Instance::try_resolve(tcx, typing_env, def_id, args) {
        Ok(Some(instance)) if tcx.is_closure_like(instance.def_id()) => {
            Callee::Closure(std::mem::discriminant(&instance.def))
        }
        Ok(Some(instance)) => Callee::Method(
            std::mem::discriminant(&instance.def),
            instance.def_id(),
            instance.args,
        ),
        Ok(None) | Err(_) => Callee::Unresolved(def_id, args),
    }
}

/// Whether `def_id` is an item of Thrust's own (`#[thrust::def::..]`: a marker call or a function
/// of the specification language), which Thrust reads in place and which resolves to no method.
fn is_thrust_item(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.get_all_attrs(def_id).iter().any(|attr| {
        let path = attr.path();
        path.len() > 2 && path[0].as_str() == "thrust" && path[1].as_str() == "def"
    })
}

/// The calls of the blocks `blocks` of `body`, whose function types `instantiate` brings into the
/// host's generics, and the closures those blocks create.
fn calls_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    body: &Body<'tcx>,
    blocks: &mut dyn Iterator<Item = BasicBlock>,
    instantiate: &dyn Fn(mir_ty::Ty<'tcx>) -> mir_ty::Ty<'tcx>,
    is_marker: &dyn Fn(DefId) -> bool,
) -> (Vec<Call<'tcx>>, Vec<LocalDefId>) {
    let mut calls = Vec::new();
    let mut closures = Vec::new();
    for bb in blocks {
        let data = &body.basic_blocks[bb];
        for statement in &data.statements {
            if let StatementKind::Assign(assign) = &statement.kind {
                if let Rvalue::Aggregate(aggregate, _) = &assign.1 {
                    if let mir::AggregateKind::Closure(def_id, _) = **aggregate {
                        closures.push(def_id.expect_local());
                    }
                }
            }
        }
        let terminator = data.terminator();
        let TerminatorKind::Call { func, .. } = &terminator.kind else {
            continue;
        };
        let fn_ty = instantiate(func.ty(&body.local_decls, tcx));
        let mir_ty::TyKind::FnDef(def_id, args) = fn_ty.kind() else {
            continue;
        };
        if is_marker(*def_id) || is_thrust_item(tcx, *def_id) {
            continue;
        }
        calls.push(Call {
            span: terminator.source_info.span,
            callee: resolve(tcx, typing_env, *def_id, args),
            written: *def_id,
        });
    }
    (calls, closures)
}

/// The calls of a closure body and of the closures below it.
fn closure_calls<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    closures: Vec<LocalDefId>,
    instantiate: &dyn Fn(mir_ty::Ty<'tcx>) -> mir_ty::Ty<'tcx>,
    is_marker: &dyn Fn(DefId) -> bool,
) -> (Vec<Call<'tcx>>, HashSet<LocalDefId>) {
    let mut calls = Vec::new();
    let mut pending = closures;
    let mut seen = HashSet::new();
    while let Some(closure) = pending.pop() {
        if !seen.insert(closure) {
            continue;
        }
        let body = tcx.optimized_mir(closure.to_def_id());
        let (found, nested) = calls_of(
            tcx,
            typing_env,
            body,
            &mut body.basic_blocks.indices(),
            instantiate,
            is_marker,
        );
        calls.extend(found);
        pending.extend(nested);
    }
    (calls, seen)
}

/// Rejects a call of the body, in `host_blocks` of `host_body`, that the extracted function `bc`,
/// instantiated with `bc_args`, would resolve to another method, or whose callee the host
/// resolves where `bc` has no call at all.
pub fn check_callees_agree<'tcx>(
    tcx: TyCtxt<'tcx>,
    host_body: &Body<'tcx>,
    host_blocks: &HashSet<BasicBlock>,
    bc: LocalDefId,
    bc_args: GenericArgsRef<'tcx>,
    is_marker: &dyn Fn(DefId) -> bool,
) {
    let root = tcx.typeck_root_def_id(host_body.source.def_id());
    let typing_env = mir_ty::TypingEnv::post_analysis(tcx, root);
    let normalize = |ty: mir_ty::Ty<'tcx>| tcx.normalize_erasing_regions(typing_env, ty);
    let into_host = |ty: mir_ty::Ty<'tcx>| {
        tcx.instantiate_and_normalize_erasing_regions(
            bc_args,
            typing_env,
            mir_ty::EarlyBinder::bind(ty),
        )
    };

    let (mut host_calls, host_closures) = calls_of(
        tcx,
        typing_env,
        host_body,
        &mut host_blocks.iter().copied(),
        &normalize,
        is_marker,
    );
    let (in_closures, host_closures) =
        closure_calls(tcx, typing_env, host_closures, &normalize, is_marker);
    host_calls.extend(in_closures);

    let bc_body = tcx.optimized_mir(bc.to_def_id());
    let (mut bc_calls, bc_closures) = calls_of(
        tcx,
        typing_env,
        bc_body,
        &mut bc_body.basic_blocks.indices(),
        &into_host,
        is_marker,
    );
    bc_calls.extend(closure_calls(tcx, typing_env, bc_closures, &into_host, is_marker).0);
    let is_host_closure = |def_id: DefId| {
        def_id
            .as_local()
            .is_some_and(|local| host_closures.contains(&local))
    };
    let is_bc_closure = |def_id: DefId| tcx.typeck_root_def_id(def_id) == bc.to_def_id();

    // a call of the extracted function that the host has no call for is an operator or a
    // conversion the host's concrete types make built in, which runs the same impl
    let mut bc_by_place: HashMap<CallPlace, Vec<Callee<'tcx>>> = HashMap::new();
    for call in bc_calls {
        bc_by_place
            .entry(call_place(call.span))
            .or_default()
            .push(call.callee.without_body_closures(tcx, &is_bc_closure));
    }
    for call in host_calls {
        let candidates = bc_by_place.entry(call_place(call.span)).or_default();
        let callee = call.callee.without_body_closures(tcx, &is_host_closure);
        if let Some(position) = candidates.iter().position(|c| *c == callee) {
            candidates.swap_remove(position);
            continue;
        }
        let other = if candidates.is_empty() {
            "has no call at this place".to_string()
        } else {
            "resolves the call to another method".to_string()
        };
        tcx.dcx().span_err(
            call.span,
            format!(
                "the body of `block_contract!` calls `{}` here, but the extracted function would \
                 call a different method (it {other}). The block is verified \
                 as the extracted function, so the method resolved there must be the one that \
                 runs in place; name the method with a path (`Trait::method(x)`) or declare the \
                 type with the bound that picks it",
                tcx.def_path_str(call.written),
            ),
        );
    }
    tcx.dcx().abort_if_errors();
}
