//! The items of the crate whose definitions may depend on a derived predicate, by `DefId`.
//!
//! A definition depends on another item when its body refers to it: a predicate or logic
//! function calls a predicate, a logic function or a trait's item; a trait's item depends on the
//! definitions of it the crate's impls give, and on its default body. The set is closed to a
//! fixed point from the derived trait items. References are read off the bodies' HIR with their
//! type-check results, so a call through `Self::produces`, `I::bounded` or a method call names
//! the item it resolves to, and the closures inside a body (the `forall(|i| ..)` of a
//! specification) are walked with it.

use std::collections::{HashMap, HashSet};

use rustc_hir::def::{DefKind, Res};
use rustc_hir::intravisit::{self, Visitor};
use rustc_middle::hir::nested_filter;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::{DefId, LocalDefId};

use crate::analyze;

/// The functions `owner`'s body refers to, nested closures' bodies included.
fn referenced_fns(tcx: TyCtxt<'_>, owner: LocalDefId) -> Vec<DefId> {
    struct Refs<'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
        out: Vec<DefId>,
    }
    impl<'tcx> Visitor<'tcx> for Refs<'tcx> {
        type NestedFilter = nested_filter::OnlyBodies;

        fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
            self.tcx
        }

        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            match &expr.kind {
                rustc_hir::ExprKind::Path(qpath) => {
                    if let Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) =
                        self.typeck.qpath_res(qpath, expr.hir_id)
                    {
                        self.out.push(def_id);
                    }
                }
                rustc_hir::ExprKind::MethodCall(..) => {
                    if let Some(def_id) = self.typeck.type_dependent_def_id(expr.hir_id) {
                        self.out.push(def_id);
                    }
                }
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let Some(body) = tcx.hir_maybe_body_owned_by(owner) else {
        return Vec::new();
    };
    let mut refs = Refs {
        tcx,
        typeck: tcx.typeck(owner),
        out: Vec::new(),
    };
    refs.visit_body(body);
    refs.out
}

/// The formula functions of `owner`'s written contract: the paths its body names under the
/// `requires`, `ensures` and `hist_inv` markers (a closure's `closure!` specification).
pub fn contract_fns(tcx: TyCtxt<'_>, owner: LocalDefId) -> Vec<DefId> {
    let markers = [
        analyze::annot::requires_path_path(),
        analyze::annot::ensures_path_path(),
        analyze::annot::hist_inv_path_path(),
    ];
    let Some(body) = tcx.hir_maybe_body_owned_by(owner) else {
        return Vec::new();
    };
    let rustc_hir::ExprKind::Block(block, _) = body.value.kind else {
        return Vec::new();
    };
    let typeck = tcx.typeck(owner);
    let mut fns = Vec::new();
    for stmt in block.stmts {
        let marked = tcx
            .hir_attrs(stmt.hir_id)
            .iter()
            .any(|attr| markers.iter().any(|m| attr.path_matches(m)));
        let rustc_hir::StmtKind::Semi(expr) = stmt.kind else {
            continue;
        };
        let rustc_hir::ExprKind::Path(qpath) = &expr.kind else {
            continue;
        };
        if let (true, Res::Def(_, def_id)) = (marked, typeck.qpath_res(qpath, expr.hir_id)) {
            fns.push(def_id);
        }
    }
    fns
}

/// The items whose definitions may depend on one of `seeds` (the derived trait items), the
/// seeds included.
pub fn dependent_items(tcx: TyCtxt<'_>, seeds: &HashSet<DefId>) -> HashSet<DefId> {
    let mut edges: HashMap<DefId, Vec<DefId>> = HashMap::new();
    for def in tcx.hir_crate_items(()).definitions() {
        if matches!(
            tcx.def_kind(def),
            DefKind::Fn | DefKind::AssocFn | DefKind::Closure
        ) {
            edges
                .entry(def.to_def_id())
                .or_default()
                .extend(referenced_fns(tcx, def));
        }
    }
    // A trait's item depends on each definition of it by an impl of the crate.
    for impls in tcx.all_local_trait_impls(()).values() {
        for impl_def_id in impls {
            for item in tcx
                .associated_items(impl_def_id.to_def_id())
                .in_definition_order()
            {
                if let Some(trait_item) = item.trait_item_def_id {
                    edges.entry(trait_item).or_default().push(item.def_id);
                }
            }
        }
    }
    let mut dependent = seeds.clone();
    loop {
        let grown: Vec<DefId> = edges
            .iter()
            .filter(|(item, refs)| {
                !dependent.contains(item) && refs.iter().any(|r| dependent.contains(r))
            })
            .map(|(item, _)| *item)
            .collect();
        if grown.is_empty() {
            return dependent;
        }
        dependent.extend(grown);
    }
}

/// Whether a trait item left out by some impl (a derived seed) is defined by another impl of
/// the crate whose definition refers to a dependent item, the seed itself included: such an
/// instance may depend on the derived predicate with either polarity.
pub fn written_dependent_instance(
    tcx: TyCtxt<'_>,
    seed: DefId,
    dependent: &HashSet<DefId>,
) -> bool {
    let Some(trait_def_id) = tcx.trait_of_assoc(seed) else {
        return true;
    };
    let impls = tcx.all_local_trait_impls(()).get(&trait_def_id);
    impls.into_iter().flatten().any(|impl_def_id| {
        let implementors = tcx.impl_item_implementor_ids(impl_def_id.to_def_id());
        implementors.get(&seed).is_some_and(|item| {
            item.as_local().is_some_and(|local| {
                referenced_fns(tcx, local)
                    .iter()
                    .any(|r| dependent.contains(r))
            })
        })
    })
}
