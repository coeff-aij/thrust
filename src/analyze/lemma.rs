//! Checks that let a lemma's contract be assumed where `proof!` does not run it: a lemma
//! terminates and changes nothing, and `proof!` calls only lemmas.
//!
//! A lemma has no loop and no closure, takes no `&mut`, and calls only functions outside the
//! crate, other lemmas without a cycle, and itself through the companion
//! `#[thrust_macros::variant]` makes, whose precondition requires the variant to decrease.

use std::collections::HashMap;

use rustc_middle::mir::visit::Visitor;
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
            && !self.has_attr(id, &analyze::annot::extern_spec_fn_path())
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

    /// Each use of `__proof_branch` in `def_id` is the condition of a `proof!` branch: the
    /// branch taken on it makes one lemma call and nothing else the program after it can see,
    /// so that not running it leaves the program as the analysis describes it.
    fn check_proof_branches(&self, def_id: LocalDefId, proof_branch: DefId) {
        let body = self.tcx.optimized_mir(def_id);
        let mut uses = Uses {
            proof_branch,
            local_blocks: HashMap::new(),
            proof_branch_constants: 0,
        };
        uses.visit_body(body);
        let mut calls = 0;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let TerminatorKind::Call {
                func,
                destination,
                target,
                fn_span,
                ..
            } = &data.terminator().kind
            else {
                continue;
            };
            if func.const_fn_def().map(|(def_id, _)| def_id) != Some(proof_branch) {
                continue;
            }
            calls += 1;
            if !self.is_proof_branch(body, &uses, block, *destination, *target) {
                self.tcx.dcx().span_err(
                    *fn_span,
                    "`__proof_branch()` is only the condition of a `proof!`, which makes one lemma call",
                );
            }
        }
        if uses.proof_branch_constants != calls {
            self.tcx
                .dcx()
                .span_err(body.span, "`__proof_branch` is only called, by `proof!`");
        }
    }

    fn is_proof_branch(
        &self,
        body: &mir::Body<'tcx>,
        uses: &Uses,
        call: mir::BasicBlock,
        destination: mir::Place<'tcx>,
        target: Option<mir::BasicBlock>,
    ) -> bool {
        let (Some(switch), Some(cond)) = (target, destination.as_local()) else {
            return false;
        };
        let data = &body.basic_blocks[switch];
        if !data.statements.iter().all(|stmt| is_marker(&stmt.kind)) {
            return false;
        }
        let TerminatorKind::SwitchInt { discr, targets } = &data.terminator().kind else {
            return false;
        };
        if discr.place().and_then(|place| place.as_local()) != Some(cond) {
            return false;
        }
        let [(0, join)] = targets.iter().collect::<Vec<_>>()[..] else {
            return false;
        };
        if !uses.only_in(cond, &[call, switch]) {
            return false;
        }
        let Some((path, assigned)) = self.lemma_call_path(body, switch, targets.otherwise(), join)
        else {
            return false;
        };
        assigned.into_iter().all(|local| uses.only_in(local, &path))
    }

    /// The blocks from `then` to `join`, and the locals they assign, when the blocks form a
    /// straight path entered only from `switch` and do nothing but assign locals and make one
    /// call, of a lemma.
    fn lemma_call_path(
        &self,
        body: &mir::Body<'tcx>,
        switch: mir::BasicBlock,
        then: mir::BasicBlock,
        join: mir::BasicBlock,
    ) -> Option<(Vec<mir::BasicBlock>, Vec<mir::Local>)> {
        let predecessors = body.basic_blocks.predecessors();
        let mut path = Vec::new();
        let mut assigned = Vec::new();
        let mut lemma_calls = 0;
        let (mut prev, mut block) = (switch, then);
        while block != join {
            if path.contains(&block) || predecessors[block].as_slice() != [prev] {
                return None;
            }
            let data = &body.basic_blocks[block];
            for stmt in &data.statements {
                match &stmt.kind {
                    mir::StatementKind::Assign(assign) => assigned.push(assign.0.as_local()?),
                    kind if is_marker(kind) => {}
                    _ => return None,
                }
            }
            let next = match &data.terminator().kind {
                TerminatorKind::Goto { target } => *target,
                TerminatorKind::Call {
                    func,
                    destination,
                    target: Some(target),
                    ..
                } if func
                    .const_fn_def()
                    .is_some_and(|(def_id, _)| self.is_lemma(def_id)) =>
                {
                    lemma_calls += 1;
                    assigned.push(destination.as_local()?);
                    *target
                }
                _ => return None,
            };
            path.push(block);
            prev = block;
            block = next;
        }
        (lemma_calls == 1).then_some((path, assigned))
    }
}

fn is_marker(kind: &mir::StatementKind<'_>) -> bool {
    matches!(
        kind,
        mir::StatementKind::StorageLive(_)
            | mir::StatementKind::StorageDead(_)
            | mir::StatementKind::Nop
    )
}

/// The blocks each local is mentioned in, and how often `__proof_branch` appears as a value.
struct Uses {
    proof_branch: DefId,
    local_blocks: HashMap<mir::Local, Vec<mir::BasicBlock>>,
    proof_branch_constants: usize,
}

impl Uses {
    fn only_in(&self, local: mir::Local, blocks: &[mir::BasicBlock]) -> bool {
        self.local_blocks
            .get(&local)
            .into_iter()
            .flatten()
            .all(|block| blocks.contains(block))
    }
}

impl<'tcx> Visitor<'tcx> for Uses {
    fn visit_local(
        &mut self,
        local: mir::Local,
        _context: mir::visit::PlaceContext,
        location: mir::Location,
    ) {
        self.local_blocks
            .entry(local)
            .or_default()
            .push(location.block);
    }

    fn visit_var_debug_info(&mut self, _var_debug_info: &mir::VarDebugInfo<'tcx>) {}

    fn visit_const_operand(
        &mut self,
        constant: &mir::ConstOperand<'tcx>,
        _location: mir::Location,
    ) {
        if let mir_ty::FnDef(def_id, _) = constant.const_.ty().kind() {
            if *def_id == self.proof_branch {
                self.proof_branch_constants += 1;
            }
        }
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
