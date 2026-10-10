//! Checks that let a lemma's contract be assumed where `proof!` does not run it: a lemma
//! terminates and changes nothing, and `proof!` calls only lemmas.
//!
//! A lemma has no loop and no closure, takes no `&mut`, and calls only functions outside the
//! crate, other lemmas without a cycle, and itself through the companion
//! `#[thrust_macros::variant]` makes, whose precondition requires the variant to decrease.

use std::collections::HashMap;

use rustc_middle::mir::{self, TerminatorKind};
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::analyze;

pub fn check(tcx: TyCtxt<'_>, proof_branch: Option<DefId>) {
    let checker = Checker { tcx };
    let lemmas: Vec<LocalDefId> = tcx
        .mir_keys(())
        .iter()
        .copied()
        .filter(|def_id| checker.is_lemma(def_id.to_def_id()))
        .collect();
    let mut calls = HashMap::new();
    for &lemma in &lemmas {
        checker.check_signature(lemma);
        calls.insert(lemma, checker.lemma_calls(lemma));
    }
    checker.check_acyclic(&lemmas, &calls);
    if let Some(proof_branch) = proof_branch {
        for &def_id in tcx.mir_keys(()) {
            if checker.has_plain_body(def_id) {
                checker.check_proof_branches(def_id, proof_branch);
            }
        }
    }
    tcx.dcx().abort_if_errors();
}

struct Checker<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Checker<'tcx> {
    fn has_attr(&self, def_id: DefId, path: &[rustc_span::Symbol]) -> bool {
        self.tcx.get_attrs_by_path(def_id, path).next().is_some()
    }

    fn is_lemma(&self, def_id: DefId) -> bool {
        self.has_attr(def_id, &analyze::annot::lemma_path())
    }

    fn is_injected_std(&self, def_id: LocalDefId) -> bool {
        let span = self.tcx.def_span(def_id);
        matches!(
            self.tcx.sess.source_map().span_to_filename(span),
            rustc_span::FileName::Custom(name) if name == crate::INJECTED_STD_FILE_NAME
        )
    }

    /// Whether `def_id` is a function with an executable body written in this crate.
    fn has_plain_body(&self, def_id: LocalDefId) -> bool {
        let id = def_id.to_def_id();
        self.tcx.def_kind(id).is_fn_like()
            && !self.is_injected_std(def_id)
            && !self.has_attr(id, &analyze::annot::formula_fn_path())
            && !self.has_attr(id, &analyze::annot::predicate_path())
            && !self.has_attr(id, &analyze::annot::ignored_path())
            && self.tcx.is_mir_available(id)
    }

    fn check_signature(&self, lemma: LocalDefId) {
        let sig = self.tcx.fn_sig(lemma).instantiate_identity().skip_binder();
        let takes_mut = sig.inputs().iter().any(|ty| {
            ty.walk().any(|arg| {
                arg.as_type().is_some_and(|ty| {
                    matches!(ty.kind(), mir_ty::Ref(_, _, mir_ty::Mutability::Mut))
                })
            })
        });
        if takes_mut {
            self.tcx
                .dcx()
                .span_err(self.tcx.def_span(lemma), "a lemma cannot take a `&mut`");
        }
    }

    /// The lemmas `lemma` calls, other than itself under its variant, after checking that it
    /// calls nothing else that could fail to terminate.
    fn lemma_calls(&self, lemma: LocalDefId) -> Vec<(LocalDefId, rustc_span::Span)> {
        let body = self.tcx.optimized_mir(lemma);
        let dcx = self.tcx.dcx();
        if rustc_data_structures::graph::is_cyclic(&body.basic_blocks) {
            dcx.span_err(loop_span(body), "a lemma cannot contain a loop");
        }
        for decl in &body.local_decls {
            if matches!(decl.ty.kind(), mir_ty::Closure(..) | mir_ty::Coroutine(..)) {
                dcx.span_err(decl.source_info.span, "a lemma cannot contain a closure");
            }
        }
        let mut lemmas = Vec::new();
        for data in body.basic_blocks.iter() {
            let terminator = data.terminator();
            match &terminator.kind {
                TerminatorKind::Call { func, fn_span, .. } => {
                    if let Some(callee) = self.lemma_callee(lemma, func, *fn_span) {
                        lemmas.push((callee, *fn_span));
                    }
                }
                TerminatorKind::Drop { place, .. } => {
                    self.check_drop(place.ty(body, self.tcx).ty, terminator.source_info.span)
                }
                _ => {}
            }
        }
        lemmas
    }

    fn lemma_callee(
        &self,
        lemma: LocalDefId,
        func: &mir::Operand<'tcx>,
        span: rustc_span::Span,
    ) -> Option<LocalDefId> {
        let dcx = self.tcx.dcx();
        let Some((def_id, args)) = func.const_fn_def() else {
            dcx.span_err(span, "a lemma calls functions only by name");
            return None;
        };
        let Some(local) = def_id.as_local() else {
            self.check_external_callee(lemma, def_id, args, span);
            return None;
        };
        if self.is_lemma(def_id) {
            if local == lemma {
                dcx.span_err(
                    span,
                    "a lemma calling itself needs #[thrust_macros::variant(..)]",
                );
                return None;
            }
            return Some(local);
        }
        if self.has_attr(def_id, &analyze::annot::lemma_rec_path()) {
            let target = self.rec_target(local);
            return (target != lemma).then_some(target);
        }
        if !self.is_injected_std(local) {
            dcx.span_err(
                span,
                "a lemma calls only lemmas and functions outside the crate",
            );
        }
        None
    }

    /// A function outside the crate is assumed to terminate, unless it resolves to an
    /// implementation in this crate or cannot be resolved yet.
    fn check_external_callee(
        &self,
        lemma: LocalDefId,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        span: rustc_span::Span,
    ) {
        let typing_env = mir_ty::TypingEnv::post_analysis(self.tcx, lemma.to_def_id());
        let instance = mir_ty::Instance::try_resolve(self.tcx, typing_env, def_id, args)
            .ok()
            .flatten();
        let resolved_in_crate = instance.is_some_and(|instance| {
            instance.def_id().as_local().is_some_and(|local| {
                !self.is_injected_std(local) && !self.is_lemma(local.to_def_id())
            })
        });
        if instance.is_none() || resolved_in_crate {
            self.tcx.dcx().span_err(
                span,
                "a lemma calls only lemmas and functions outside the crate",
            );
        }
    }

    fn check_drop(&self, ty: mir_ty::Ty<'tcx>, span: rustc_span::Span) {
        let runs_local_code = ty.walk().any(|arg| {
            arg.as_type().is_some_and(|ty| match ty.kind() {
                mir_ty::Adt(adt, _) => self
                    .tcx
                    .adt_destructor(adt.did())
                    .is_some_and(|dtor| dtor.did.is_local()),
                _ => false,
            })
        });
        if runs_local_code {
            self.tcx.dcx().span_err(
                span,
                "a lemma cannot drop a value whose destructor is in the crate",
            );
        }
    }

    /// The lemma a `#[thrust::lemma_rec]` companion calls.
    fn rec_target(&self, rec: LocalDefId) -> LocalDefId {
        let body = self.tcx.optimized_mir(rec);
        body.basic_blocks
            .iter()
            .find_map(|data| match &data.terminator().kind {
                TerminatorKind::Call { func, .. } => func
                    .const_fn_def()
                    .and_then(|(def_id, _)| def_id.as_local())
                    .filter(|def_id| self.is_lemma(def_id.to_def_id())),
                _ => None,
            })
            .expect("a lemma's companion calls the lemma")
    }

    fn check_acyclic(
        &self,
        lemmas: &[LocalDefId],
        calls: &HashMap<LocalDefId, Vec<(LocalDefId, rustc_span::Span)>>,
    ) {
        let mut done = Vec::new();
        for &lemma in lemmas {
            self.visit(lemma, calls, &mut Vec::new(), &mut done);
        }
    }

    fn visit(
        &self,
        lemma: LocalDefId,
        calls: &HashMap<LocalDefId, Vec<(LocalDefId, rustc_span::Span)>>,
        path: &mut Vec<LocalDefId>,
        done: &mut Vec<LocalDefId>,
    ) {
        if done.contains(&lemma) {
            return;
        }
        path.push(lemma);
        for &(callee, span) in calls.get(&lemma).into_iter().flatten() {
            if path.contains(&callee) {
                self.tcx
                    .dcx()
                    .span_err(span, "mutual recursion between lemmas is not supported");
                continue;
            }
            self.visit(callee, calls, path, done);
        }
        path.pop();
        done.push(lemma);
    }

    /// Each `proof!` in `def_id` calls a lemma: the branch taken on `__proof_branch()` starts
    /// with a call to one.
    fn check_proof_branches(&self, def_id: LocalDefId, proof_branch: DefId) {
        let body = self.tcx.optimized_mir(def_id);
        for data in body.basic_blocks.iter() {
            let TerminatorKind::Call {
                func,
                target: Some(target),
                fn_span,
                ..
            } = &data.terminator().kind
            else {
                continue;
            };
            if func.const_fn_def().map(|(def_id, _)| def_id) != Some(proof_branch) {
                continue;
            }
            if !self.branch_calls_lemma(body, *target) {
                self.tcx
                    .dcx()
                    .span_err(*fn_span, "`proof!` takes a call of a lemma");
            }
        }
    }

    fn branch_calls_lemma(&self, body: &mir::Body<'tcx>, switch: mir::BasicBlock) -> bool {
        let TerminatorKind::SwitchInt { targets, .. } =
            &body.basic_blocks[switch].terminator().kind
        else {
            return false;
        };
        let mut block = targets.otherwise();
        for _ in 0..body.basic_blocks.len() {
            match &body.basic_blocks[block].terminator().kind {
                TerminatorKind::Goto { target } => block = *target,
                TerminatorKind::Call { func, .. } => {
                    return func
                        .const_fn_def()
                        .is_some_and(|(def_id, _)| self.is_lemma(def_id));
                }
                _ => return false,
            }
        }
        false
    }
}

/// The span of a jump back to a loop header in `body`.
fn loop_span(body: &mir::Body<'_>) -> rustc_span::Span {
    let dominators = body.basic_blocks.dominators();
    body.basic_blocks
        .iter_enumerated()
        .find_map(|(block, data)| {
            let terminator = data.terminator();
            terminator
                .successors()
                .any(|succ| dominators.dominates(succ, block))
                .then_some(terminator.source_info.span)
        })
        .unwrap_or(body.span)
}
