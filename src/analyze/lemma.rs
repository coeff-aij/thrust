//! Checks that let a lemma's contract be assumed where `proof!` does not run it: a lemma
//! terminates and changes nothing, and `proof!` calls only lemmas.
//!
//! As in Verus's proof mode and Creusot's ghost code, a lemma calls only what is known to
//! terminate without effects: other lemmas without a cycle, itself through the companion
//! `#[thrust_macros::variant]` makes (whose precondition requires the variant to decrease),
//! logic functions and predicates, and the model operations of the injected `thrust_models`.
//! The operations MIR has as statements (arithmetic, comparisons, field and index access) need
//! no call. A lemma has no loop, and takes no `&mut`, so that what it assigns stays its own.

use std::collections::HashMap;

use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{self, TerminatorKind};
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::analyze;

/// `analyzes_body` tells the functions whose bodies the analysis reads, where a `proof!` branch
/// it takes and the program does not must change nothing.
pub fn check(
    tcx: TyCtxt<'_>,
    proof_branch: Option<DefId>,
    analyzes_body: impl Fn(LocalDefId) -> bool,
) {
    let checker = Checker { tcx, proof_branch };
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
            let id = def_id.to_def_id();
            if tcx.def_kind(id).is_fn_like() && analyzes_body(def_id) && tcx.is_mir_available(id) {
                checker.check_proof_branches(def_id, proof_branch);
            }
        }
    }
    tcx.dcx().abort_if_errors();
}

struct Checker<'tcx> {
    tcx: TyCtxt<'tcx>,
    proof_branch: Option<DefId>,
}

impl<'tcx> Checker<'tcx> {
    fn has_attr(&self, def_id: DefId, path: &[rustc_span::Symbol]) -> bool {
        self.tcx.get_attrs_by_path(def_id, path).next().is_some()
    }

    fn is_lemma(&self, def_id: DefId) -> bool {
        self.has_attr(def_id, &analyze::annot::lemma_path())
    }

    fn is_lemma_rec(&self, def_id: DefId) -> bool {
        self.has_attr(def_id, &analyze::annot::lemma_rec_path())
    }

    /// The types a value of `ty` is made of: the types `ty` names and, through the fields of
    /// each struct, enum or union among them, the types of the values it holds.
    fn contained_types(&self, ty: mir_ty::Ty<'tcx>) -> Vec<mir_ty::Ty<'tcx>> {
        let mut seen = Vec::new();
        let mut pending = vec![ty];
        while let Some(ty) = pending.pop() {
            for ty in ty.walk().filter_map(|arg| arg.as_type()) {
                if seen.contains(&ty) {
                    continue;
                }
                seen.push(ty);
                if let mir_ty::Adt(adt, args) = ty.kind() {
                    pending.extend(adt.all_fields().map(|field| field.ty(self.tcx, args)));
                }
            }
        }
        seen
    }

    /// A lemma takes nothing it could change the program's state through, so that not running
    /// it changes nothing.
    fn check_signature(&self, lemma: LocalDefId) {
        let sig = self.tcx.fn_sig(lemma).instantiate_identity().skip_binder();
        let takes_mut = sig.inputs().iter().any(|ty| {
            self.contained_types(*ty)
                .iter()
                .any(|ty| matches!(ty.kind(), mir_ty::Ref(_, _, mir_ty::Mutability::Mut)))
        });
        if takes_mut {
            self.tcx.dcx().span_err(
                self.tcx.def_span(lemma),
                "a lemma cannot take a `&mut`, or a value holding one",
            );
        }
    }

    /// Whether `def_id` is a function a lemma may call besides lemmas: a logic function or
    /// predicate, or a model operation of the injected `thrust_models`, which has no effect and
    /// is never run.
    fn is_ghost_fn(&self, def_id: DefId) -> bool {
        let spec = [
            analyze::annot::logic_path(),
            analyze::annot::predicate_path(),
            analyze::annot::formula_fn_path(),
        ];
        let model_operation = def_id
            .as_local()
            .is_some_and(|local| analyze::is_injected_std(self.tcx, local))
            && (self.has_attr(def_id, &analyze::annot::ignored_path())
                || Some(def_id) == self.proof_branch);
        spec.iter().any(|path| self.has_attr(def_id, path)) || model_operation
    }

    /// The lemmas `lemma` calls, other than itself under its variant, after checking that it
    /// calls nothing else that could fail to terminate.
    fn lemma_calls(&self, lemma: LocalDefId) -> Vec<(LocalDefId, rustc_span::Span)> {
        let body = self.tcx.optimized_mir(lemma);
        let dcx = self.tcx.dcx();
        if rustc_data_structures::graph::is_cyclic(&body.basic_blocks) {
            dcx.span_err(loop_span(body), "a lemma cannot contain a loop");
        }
        let mut lemmas = Vec::new();
        for data in body.basic_blocks.iter() {
            let terminator = data.terminator();
            match &terminator.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    fn_span,
                    ..
                } => {
                    if let Some(callee) = self.lemma_callee(lemma, body, func, args, *fn_span) {
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

    /// The lemma a call in `lemma` makes, other than to itself under its variant, after checking
    /// that the callee is one a lemma may call.
    fn lemma_callee(
        &self,
        lemma: LocalDefId,
        body: &mir::Body<'tcx>,
        func: &mir::Operand<'tcx>,
        call_args: &[rustc_span::source_map::Spanned<mir::Operand<'tcx>>],
        span: rustc_span::Span,
    ) -> Option<LocalDefId> {
        let dcx = self.tcx.dcx();
        let callee = func.const_fn_def().map(|(def_id, _)| def_id);
        if callee.is_some_and(|def_id| self.is_ghost_fn(def_id)) {
            return None;
        }
        let Some(local) = callee
            .filter(|def_id| self.is_lemma(*def_id) || self.is_lemma_rec(*def_id))
            .and_then(DefId::as_local)
        else {
            dcx.span_err(
                span,
                "a lemma calls only lemmas, logic functions, predicates and model operations",
            );
            return None;
        };
        if self.is_lemma(local.to_def_id()) {
            if local == lemma {
                dcx.span_err(
                    span,
                    "a lemma calling itself needs #[thrust_macros::variant(..)]",
                );
                return None;
            }
            return Some(local);
        }
        let target = self.rec_target(local);
        if target != lemma {
            return Some(target);
        }
        if !passes_own_entries(body, call_args) {
            dcx.span_err(
                span,
                "a lemma's recursive call passes the lemma's own parameters as the entry values",
            );
        }
        None
    }

    fn check_drop(&self, ty: mir_ty::Ty<'tcx>, span: rustc_span::Span) {
        let runs_local_code = self
            .contained_types(ty)
            .into_iter()
            .any(|ty| match ty.kind() {
                mir_ty::Adt(adt, _) => self
                    .tcx
                    .adt_destructor(adt.did())
                    .is_some_and(|dtor| dtor.did.is_local()),
                _ => false,
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

/// Whether the first arguments of a call `body` makes to its own `#[thrust::lemma_rec]`
/// companion are references to `body`'s parameters, in order: the values on entry that the
/// companion's precondition compares the variant with.
fn passes_own_entries(
    body: &mir::Body<'_>,
    args: &[rustc_span::source_map::Spanned<mir::Operand<'_>>],
) -> bool {
    body.args_iter().zip(args).all(|(param, arg)| {
        arg.node
            .place()
            .and_then(|place| place.as_local())
            .and_then(|local| referent(body, local))
            == Some(param)
    })
}

/// The local that `local` holds a shared reference to, following copies, when each local on
/// the way is assigned once.
fn referent(body: &mir::Body<'_>, mut local: mir::Local) -> Option<mir::Local> {
    loop {
        let mut assignments = body.basic_blocks.iter().flat_map(|data| {
            data.statements.iter().filter_map(|stmt| match &stmt.kind {
                mir::StatementKind::Assign(assign) if assign.0.as_local() == Some(local) => {
                    Some(&assign.1)
                }
                _ => None,
            })
        });
        let (Some(rvalue), None) = (assignments.next(), assignments.next()) else {
            return None;
        };
        let assigned_by_call = body.basic_blocks.iter().any(|data| {
            matches!(&data.terminator().kind, TerminatorKind::Call { destination, .. } if destination.as_local() == Some(local))
        });
        if assigned_by_call {
            return None;
        }
        match rvalue {
            mir::Rvalue::Ref(_, mir::BorrowKind::Shared, place) => return place.as_local(),
            mir::Rvalue::Use(mir::Operand::Copy(place) | mir::Operand::Move(place)) => {
                local = place.as_local()?;
            }
            _ => return None,
        }
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
