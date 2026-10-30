//! Checks that let a lemma's contract be assumed where `proof!` does not run it: a lemma
//! terminates and changes nothing, and `proof!` calls only lemmas.
//!
//! As in Verus's proof mode and Creusot's ghost code, a lemma calls only what is known to
//! terminate without effects: other lemmas without a cycle, itself through the companion
//! `#[thrust_macros::variant]` makes (whose precondition requires the variant to decrease),
//! logic functions and predicates, and the model operations of the injected `thrust_models`.
//! The operations MIR has as statements (arithmetic, comparisons, field and index access) need
//! no call. A lemma has no loop and no unsafe code, and takes no `&mut`, so that what it
//! assigns stays its own.

use std::collections::{HashMap, HashSet};

use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{self, TerminatorKind};
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::analyze;

/// Checks every lemma of the crate; the errors are reported with those of
/// [`check_proof_branches`].
pub fn check_lemmas(tcx: TyCtxt<'_>, proof_branch: Option<DefId>) {
    let checker = Checker { tcx, proof_branch };
    // A law's proof, an impl's definition of a law or a trait's default body for one, is a
    // lemma too: what it proves is assumed wherever the trait is used through a type parameter,
    // so a proof that does not return would prove anything.
    let lemmas: Vec<LocalDefId> = tcx
        .mir_keys(())
        .iter()
        .copied()
        .filter(|def_id| {
            checker.is_lemma(def_id.to_def_id()) || checker.is_law_proof(def_id.to_def_id())
        })
        .collect();
    checker.check_impl_lemmas();
    let mut calls = HashMap::new();
    for &lemma in &lemmas {
        // A law is run where it is called, and a call analyzed as any other, so it may take a
        // `&mut`.
        if checker.is_lemma(lemma.to_def_id()) {
            checker.check_signature(lemma);
        }
        checker.check_safe(lemma);
        calls.insert(lemma, checker.proof_calls(lemma));
    }
    checker.check_acyclic(&lemmas, &calls);
    checker.check_law_uses(&lemmas, &calls);
}

/// Whether `def_id` is a lemma or a law's proof, whose contract is assumed where it does not run.
pub fn is_proof(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let checker = Checker {
        tcx,
        proof_branch: None,
    };
    checker.is_lemma(def_id) || checker.is_lemma_rec(def_id) || checker.is_law_proof(def_id)
}

/// The logic function laws of the crate (lemmas marked law outside a trait, see [`Checker::is_logic_fn_law`]).
pub fn logic_fn_laws(tcx: TyCtxt<'_>) -> Vec<LocalDefId> {
    let checker = Checker {
        tcx,
        proof_branch: None,
    };
    tcx.mir_keys(())
        .iter()
        .copied()
        .filter(|def_id| checker.is_logic_fn_law(def_id.to_def_id()))
        .collect()
}

/// `lemma` and the lemmas its proof calls, directly or through others, with the companion through
/// which each of them calls itself. They are the proof of a logic function law, which assumes no
/// such law and uses no trait law at a type parameter, since an impl's proof of that trait law may
/// assume the logic function law.
pub fn proof_closure(tcx: TyCtxt<'_>, lemma: LocalDefId) -> HashSet<LocalDefId> {
    let checker = Checker {
        tcx,
        proof_branch: None,
    };
    let mut seen = HashSet::new();
    let mut pending = vec![lemma];
    while let Some(lemma) = pending.pop() {
        if !seen.insert(lemma) {
            continue;
        }
        let calls = checker.proof_calls(lemma);
        for call in &calls.laws {
            tcx.dcx().span_err(
                call.span,
                "the proof of a law outside a trait cannot use a trait law at a type parameter",
            );
        }
        pending.extend(
            calls
                .lemmas
                .iter()
                .filter_map(|call| call.def_id.as_local()),
        );
    }
    let companions: Vec<LocalDefId> = tcx
        .mir_keys(())
        .iter()
        .copied()
        .filter(|def_id| {
            checker.is_lemma_rec(def_id.to_def_id()) && seen.contains(&checker.rec_target(*def_id))
        })
        .collect();
    seen.extend(companions);
    seen
}

/// Checks the `proof!` branches of the functions whose bodies the analysis reads
/// (`analyzes_body`), where a branch it takes and the program does not must change nothing.
pub fn check_proof_branches(
    tcx: TyCtxt<'_>,
    proof_branch: Option<DefId>,
    analyzes_body: impl Fn(LocalDefId) -> bool,
) {
    if let Some(proof_branch) = proof_branch {
        let checker = Checker {
            tcx,
            proof_branch: Some(proof_branch),
        };
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

/// A call a lemma or a law's proof makes, at generic arguments in the caller's own parameters.
#[derive(Clone, Copy)]
struct Call<'tcx> {
    def_id: DefId,
    args: mir_ty::GenericArgsRef<'tcx>,
    span: rustc_span::Span,
}

/// The calls a proof rests on: the lemmas it calls, other than itself under its variant, and
/// the laws it calls at a type parameter.
#[derive(Default)]
struct ProofCalls<'tcx> {
    lemmas: Vec<Call<'tcx>>,
    laws: Vec<Call<'tcx>>,
}

type Calls<'tcx> = HashMap<LocalDefId, ProofCalls<'tcx>>;

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

    fn is_law(&self, def_id: DefId) -> bool {
        self.has_attr(def_id, &analyze::annot::law_path())
    }

    /// Whether `def_id` is a law outside a trait: a lemma whose contract is assumed wherever a
    /// function it applies is (`crate_::Analyzer::assume_logic_fn_laws`).
    fn is_logic_fn_law(&self, def_id: DefId) -> bool {
        self.is_law(def_id) && self.tcx.opt_associated_item(def_id).is_none()
    }

    /// Whether `def_id` is a trait law with a default body or an impl's definition of one.
    fn is_law_proof(&self, def_id: DefId) -> bool {
        self.is_law(def_id)
            || self
                .tcx
                .opt_associated_item(def_id)
                .and_then(|item| item.trait_item_def_id)
                .is_some_and(|trait_item| self.is_law(trait_item))
    }

    /// Whether a call of `def_id` at `args` is of a law at a type parameter other than `Self`,
    /// whose proof is another impl's or, in a law's proof, has to be (see
    /// [`Self::check_law_uses`]). A law used at `Self` or at a concrete type could be the one
    /// being proved.
    fn is_law_at_type_param(&self, def_id: DefId, args: mir_ty::GenericArgsRef<'tcx>) -> bool {
        if !self.is_law(def_id) || self.is_logic_fn_law(def_id) {
            return false;
        }
        let ty = args.type_at(0);
        matches!(ty.kind(), mir_ty::Param(param) if param.name != rustc_span::symbol::kw::SelfUpper)
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

    /// A lemma has no unsafe code, as in Verus's proof mode: it is not an `unsafe fn` and has
    /// no `unsafe` block, so it cannot write through a raw pointer, and it takes no raw pointer
    /// (`&raw`) either.
    fn check_safe(&self, lemma: LocalDefId) {
        if self.tcx.fn_sig(lemma).skip_binder().safety().is_unsafe() {
            self.tcx
                .dcx()
                .span_err(self.tcx.def_span(lemma), "a lemma cannot be unsafe");
        }
        let mut finder = UnsafeFinder { spans: Vec::new() };
        rustc_hir::intravisit::Visitor::visit_body(&mut finder, self.tcx.hir_body_owned_by(lemma));
        for span in finder.spans {
            self.tcx.dcx().span_err(
                span,
                "a lemma cannot contain an `unsafe` block or a raw pointer",
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
            && (analyze::is_ignored(self.tcx, def_id) || Some(def_id) == self.proof_branch);
        spec.iter().any(|path| self.has_attr(def_id, path)) || model_operation
    }

    /// The lemmas and the laws `lemma` calls, after checking that it calls nothing else that
    /// could fail to terminate.
    fn proof_calls(&self, lemma: LocalDefId) -> ProofCalls<'tcx> {
        let body = self.tcx.optimized_mir(lemma);
        let dcx = self.tcx.dcx();
        if rustc_data_structures::graph::is_cyclic(&body.basic_blocks) {
            dcx.span_err(
                loop_span(body),
                "a lemma or a law's proof cannot contain a loop",
            );
        }
        let mut calls = ProofCalls::default();
        for data in body.basic_blocks.iter() {
            let terminator = data.terminator();
            match &terminator.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    fn_span,
                    ..
                } => self.add_call(&mut calls, lemma, body, func, args, *fn_span),
                TerminatorKind::Drop { place, .. } => {
                    self.check_drop(place.ty(body, self.tcx).ty, terminator.source_info.span)
                }
                _ => {}
            }
        }
        calls
    }

    /// Adds a call in `lemma` to `calls`, after checking that the callee is one a lemma may
    /// call.
    fn add_call(
        &self,
        calls: &mut ProofCalls<'tcx>,
        lemma: LocalDefId,
        body: &mir::Body<'tcx>,
        func: &mir::Operand<'tcx>,
        call_args: &[rustc_span::source_map::Spanned<mir::Operand<'tcx>>],
        span: rustc_span::Span,
    ) {
        let dcx = self.tcx.dcx();
        let Some((def_id, args)) = func.const_fn_def() else {
            dcx.span_err(span, CALLEE_ERROR);
            return;
        };
        if self.is_ghost_fn(def_id) {
            return;
        }
        if self.is_law_at_type_param(def_id, args) {
            calls.laws.push(Call { def_id, args, span });
            return;
        }
        let Some((def_id, args)) = self.resolve_trait_lemma(lemma, def_id, args, span) else {
            return;
        };
        let Some(local) = def_id
            .as_local()
            .filter(|_| self.is_lemma(def_id) || self.is_lemma_rec(def_id))
        else {
            dcx.span_err(span, CALLEE_ERROR);
            return;
        };
        if self.is_lemma(def_id) {
            if local == lemma {
                dcx.span_err(
                    span,
                    "a lemma calling itself needs #[thrust_macros::variant(..)]",
                );
                return;
            }
            calls.lemmas.push(Call { def_id, args, span });
            return;
        }
        // The companion has the lemma's generics and calls it at its own arguments.
        let target = self.rec_target(local);
        if target != lemma {
            calls.lemmas.push(Call {
                def_id: target.to_def_id(),
                args,
                span,
            });
            return;
        }
        if !passes_own_entries(body, call_args) {
            dcx.span_err(
                span,
                "a lemma's recursive call passes the lemma's own parameters as the entry values",
            );
        }
        // A recursive call at other arguments could use a law at a larger type at each step.
        let identity = mir_ty::GenericArgs::identity_for_item(self.tcx, lemma);
        if self.tcx.erase_regions(args) != self.tcx.erase_regions(identity) {
            dcx.span_err(
                span,
                "a lemma's recursive call is at the lemma's own generic arguments",
            );
        }
    }

    /// The function a call of a trait's lemma runs: the impl's lemma, or the trait's default body
    /// at the impl's arguments. A call that resolves to no impl, at a type parameter, could run
    /// any impl's, which [`Self::check_acyclic`] and [`Self::check_law_uses`] cannot follow, and is
    /// rejected. A call of a free function is its own.
    fn resolve_trait_lemma(
        &self,
        caller: LocalDefId,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        span: rustc_span::Span,
    ) -> Option<(DefId, mir_ty::GenericArgsRef<'tcx>)> {
        if self.tcx.trait_of_assoc(def_id).is_none() || !self.is_lemma(def_id) {
            return Some((def_id, args));
        }
        let typing_env = mir_ty::TypingEnv::post_analysis(self.tcx, caller);
        if let Ok(Some(instance)) =
            mir_ty::Instance::try_resolve(self.tcx, typing_env, def_id, args)
        {
            return Some((instance.def_id(), instance.args));
        }
        self.tcx.dcx().span_err(
            span,
            "a lemma or a law's proof calls a trait's lemma only at a type that selects its impl",
        );
        None
    }

    /// An impl's definition of a trait's lemma is a lemma too, as Creusot and Verus require an
    /// impl item to have its trait item's mode: a call of the trait's lemma runs it, and its
    /// contract is assumed where it does not run.
    fn check_impl_lemmas(&self) {
        for &def_id in self.tcx.mir_keys(()) {
            let trait_item = self
                .tcx
                .opt_associated_item(def_id.to_def_id())
                .and_then(|item| item.trait_item_def_id);
            let Some(trait_item) = trait_item else {
                continue;
            };
            if self.is_lemma(trait_item) && !self.is_lemma(def_id.to_def_id()) {
                self.tcx.dcx().span_err(
                    self.tcx.def_span(def_id),
                    "an impl's definition of a trait's lemma is a `#[thrust_macros::lemma]` too",
                );
            }
        }
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

    fn check_acyclic(&self, lemmas: &[LocalDefId], calls: &Calls<'tcx>) {
        let mut done = Vec::new();
        for &lemma in lemmas {
            self.visit(lemma, calls, &mut Vec::new(), &mut done);
        }
    }

    fn visit(
        &self,
        lemma: LocalDefId,
        calls: &Calls<'tcx>,
        path: &mut Vec<LocalDefId>,
        done: &mut Vec<LocalDefId>,
    ) {
        if done.contains(&lemma) {
            return;
        }
        path.push(lemma);
        for call in calls.get(&lemma).into_iter().flat_map(|c| &c.lemmas) {
            let callee = call.def_id.expect_local();
            if path.contains(&callee) {
                self.tcx.dcx().span_err(
                    call.span,
                    "mutual recursion between lemmas is not supported",
                );
                continue;
            }
            self.visit(callee, calls, path, done);
        }
        path.pop();
        done.push(lemma);
    }

    /// A law's proof uses a law only at a type parameter strictly inside the impl's self type
    /// (`T` of `Wrap<T>`), directly or through the lemmas it calls, at the arguments it calls
    /// them at. The proof of a law at a type then rests only on laws at smaller types, so the
    /// proofs are well-founded. A trait's default body is checked at each impl that inherits it,
    /// with the impl's arguments; a law at one of the law's own type parameters could be the
    /// law at the impl's self type, and is rejected.
    fn check_law_uses(&self, lemmas: &[LocalDefId], calls: &Calls<'tcx>) {
        let mut memo = HashMap::new();
        for &proof in lemmas {
            if !self.is_law_proof(proof.to_def_id()) {
                continue;
            }
            let uses = self.proof_law_uses(proof, calls, &mut memo);
            match self.tcx.impl_of_assoc(proof.to_def_id()) {
                Some(impl_did) => {
                    let identity = mir_ty::GenericArgs::identity_for_item(self.tcx, proof);
                    self.check_law_uses_at_impl(proof, impl_did, identity, &uses);
                }
                None => {
                    for (impl_did, args) in self.inheriting_impls(proof.to_def_id()) {
                        self.check_law_uses_at_impl(proof, impl_did, args, &uses);
                    }
                }
            }
        }
    }

    /// The laws `proof` uses, at arguments in its own parameters, each with the span of the
    /// call in `proof` that uses it: its own calls of laws, and those of the lemmas it calls.
    fn proof_law_uses(
        &self,
        proof: LocalDefId,
        calls: &Calls<'tcx>,
        memo: &mut HashMap<LocalDefId, Vec<Call<'tcx>>>,
    ) -> Vec<(Call<'tcx>, Option<DefId>)> {
        let Some(proof_calls) = calls.get(&proof) else {
            return Vec::new();
        };
        let direct = proof_calls.laws.iter().map(|call| (*call, None));
        let through_lemmas = proof_calls.lemmas.iter().flat_map(|call| {
            let uses = self.lemma_law_uses(call.def_id.expect_local(), calls, memo);
            uses.into_iter().map(move |law| {
                let args = mir_ty::EarlyBinder::bind(law.args).instantiate(self.tcx, call.args);
                let law = Call {
                    def_id: law.def_id,
                    args,
                    span: call.span,
                };
                (law, Some(call.def_id))
            })
        });
        direct.chain(through_lemmas).collect()
    }

    /// The laws `lemma` uses, directly or through the lemmas it calls, at arguments in its own
    /// parameters. A cycle among lemmas is reported by [`Self::check_acyclic`] and adds nothing.
    fn lemma_law_uses(
        &self,
        lemma: LocalDefId,
        calls: &Calls<'tcx>,
        memo: &mut HashMap<LocalDefId, Vec<Call<'tcx>>>,
    ) -> Vec<Call<'tcx>> {
        if let Some(uses) = memo.get(&lemma) {
            return uses.clone();
        }
        memo.insert(lemma, Vec::new());
        let uses: Vec<_> = self
            .proof_law_uses(lemma, calls, memo)
            .into_iter()
            .map(|(law, _)| law)
            .collect();
        memo.insert(lemma, uses.clone());
        uses
    }

    /// The local impls that inherit the trait's default body `law`, each with the arguments
    /// that body is checked at there: the impl's trait arguments, and the law's own parameters.
    fn inheriting_impls(&self, law: DefId) -> Vec<(DefId, mir_ty::GenericArgsRef<'tcx>)> {
        let Some(trait_did) = self.tcx.trait_of_assoc(law) else {
            return Vec::new();
        };
        let impls = self.tcx.all_local_trait_impls(()).get(&trait_did);
        impls
            .into_iter()
            .flatten()
            .map(|impl_local| impl_local.to_def_id())
            .filter(|impl_did| {
                !self
                    .tcx
                    .impl_item_implementor_ids(*impl_did)
                    .contains_key(&law)
            })
            .map(|impl_did| {
                let trait_ref = self
                    .tcx
                    .impl_trait_ref(impl_did)
                    .unwrap()
                    .instantiate_identity();
                let args = mir_ty::GenericArgs::identity_for_item(self.tcx, law).rebase_onto(
                    self.tcx,
                    trait_did,
                    trait_ref.args,
                );
                (impl_did, args)
            })
            .collect()
    }

    /// Checks the law uses of `proof`, read at `args`, against the self type of `impl_did`.
    fn check_law_uses_at_impl(
        &self,
        proof: LocalDefId,
        impl_did: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        uses: &[(Call<'tcx>, Option<DefId>)],
    ) {
        let self_ty = self.tcx.type_of(impl_did).instantiate_identity();
        let own_params = self.tcx.generics_of(proof).parent_count;
        for (law, lemma) in uses {
            let at_own_param = matches!(
                law.args.type_at(0).kind(),
                mir_ty::Param(param) if param.index as usize >= own_params
            );
            let law_args = mir_ty::EarlyBinder::bind(law.args).instantiate(self.tcx, args);
            let ty = law_args.type_at(0);
            let inside = matches!(ty.kind(), mir_ty::Param(_))
                && self_ty != ty
                && self_ty.walk().any(|arg| arg.as_type() == Some(ty));
            if inside && !at_own_param {
                continue;
            }
            let through = lemma
                .map(|lemma| format!(" through `{}`", self.tcx.def_path_str(lemma)))
                .unwrap_or_default();
            self.tcx
                .dcx()
                .struct_span_err(
                    law.span,
                    format!(
                        "a law's proof uses a law only at a type parameter strictly inside the \
                         impl's self type `{self_ty}`, but this one uses `{}`{through}",
                        self.tcx.def_path_str_with_args(law.def_id, law_args),
                    ),
                )
                .with_span_note(self.tcx.def_span(impl_did), "in the proof for this impl")
                .emit();
        }
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

const CALLEE_ERROR: &str = "a lemma or a law's proof calls only lemmas, logic functions, \
     predicates, model operations and laws at a type parameter";

/// The `unsafe` blocks written in a body, and the raw pointers it takes (`&raw`).
struct UnsafeFinder {
    spans: Vec<rustc_span::Span>,
}

impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for UnsafeFinder {
    fn visit_block(&mut self, block: &'tcx rustc_hir::Block<'tcx>) {
        if let rustc_hir::BlockCheckMode::UnsafeBlock(rustc_hir::UnsafeSource::UserProvided) =
            block.rules
        {
            self.spans.push(block.span);
        }
        rustc_hir::intravisit::walk_block(self, block);
    }

    fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
        if let rustc_hir::ExprKind::AddrOf(rustc_hir::BorrowKind::Raw, _, _) = expr.kind {
            self.spans.push(expr.span);
        }
        rustc_hir::intravisit::walk_expr(self, expr);
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
