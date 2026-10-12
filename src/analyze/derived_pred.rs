//! Derived predicates: a trait's `#[thrust_macros::predicate(derived)]` at an impl that leaves
//! it undefined.
//!
//! Such a predicate is declared as an unknown. The clauses the impl's own bodies conclude of it
//! (its laws, its methods' contracts) are its rules, and its meaning is their least fixpoint, as
//! a loop invariant's is that of the loop's entry and back edge. Every other clause must only
//! assume it: then any solution contains the least fixpoint and every other clause stays valid
//! when it shrinks to it, so a verdict means what it would with the least fixpoint written as
//! the body, independently of the clients. A clause elsewhere that concludes it would add a
//! fact the rules do not derive, so it is reported, and the predicate must be written.

use std::collections::{HashMap, HashSet};

use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::DefId;

use crate::chc;

/// The function each clause comes from, by the range of clause indices pushed while it was
/// analyzed. Ranges nest when a body is analyzed while another is (a callee at an instance); a
/// clause belongs to the innermost.
#[derive(Debug, Clone, Default)]
pub struct ClauseSites {
    ranges: Vec<(std::ops::Range<usize>, DefId)>,
}

impl ClauseSites {
    pub fn record(&mut self, clauses: std::ops::Range<usize>, site: DefId) {
        self.ranges.push((clauses, site));
    }

    fn site_of(&self, clause: chc::ClauseId) -> Option<DefId> {
        self.ranges
            .iter()
            .filter(|(range, _)| range.contains(&clause.index()))
            .max_by_key(|(range, _)| range.start)
            .map(|(_, site)| *site)
    }
}

/// Whether `site` is a function of an impl for `self_ty`, where the rules of a derived
/// predicate of `self_ty` come from.
fn is_rule_site<'tcx>(tcx: TyCtxt<'tcx>, site: DefId, self_ty: mir_ty::Ty<'tcx>) -> bool {
    tcx.impl_of_assoc(site).is_some_and(|impl_def_id| {
        let impl_self_ty = tcx.type_of(impl_def_id).instantiate_identity();
        tcx.erase_regions(impl_self_ty) == tcx.erase_regions(self_ty)
    })
}

/// Reports each clause that concludes a derived predicate of `derived` (symbol to the `Self`
/// type it is declared at) outside the impls for that type.
pub fn check_head_closed<'tcx>(
    tcx: TyCtxt<'tcx>,
    system: &chc::System,
    sites: &ClauseSites,
    derived: &HashMap<chc::UserDefinedPred, mir_ty::Ty<'tcx>>,
) {
    let mut reported = HashSet::new();
    for (clause, pred) in system.concluded_user_defined_preds() {
        let Some(self_ty) = derived.get(pred) else {
            continue;
        };
        let site = sites.site_of(clause);
        if site.is_some_and(|site| is_rule_site(tcx, site, *self_ty)) {
            continue;
        }
        if !reported.insert((pred.clone(), site)) {
            continue;
        }
        let message = format!(
            "the derived predicate `{pred}` of `{self_ty}` is concluded outside the impls of \
             `{self_ty}`, which would add a fact its rules do not derive; define it in the impl"
        );
        match site {
            Some(site) => tcx.dcx().span_err(tcx.def_span(site), message),
            None => tcx.dcx().err(message),
        };
    }
    tcx.dcx().abort_if_errors();
}
