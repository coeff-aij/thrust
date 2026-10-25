//! Where a type with an invariant (std.rs's `Invariant`) meets code that does not check it.
//!
//! The invariant is conjoined to a contract at the positions where the signature has the type
//! (`local_def::Analyzer::conjoin_type_invariants`), read on the signature at the instance. A
//! contract established over type parameters has no conjunct where it has a type parameter. In a
//! crate with an `Invariant` impl every generic body is therefore analyzed at each instance
//! ([`analyze::Analyzer::per_instance_generics`]). What is left is code Thrust does not analyze:
//! its contract may not promise an invariant at an instance
//! ([`analyze::Analyzer::stop_promised_invariant`]), and what it runs may not assume one
//! ([`analyze::Analyzer::stop_invariant_assumed_unanalyzed`]).

use std::collections::{HashMap, HashSet};

use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::DefId;

use crate::analyze;

impl<'tcx> analyze::Analyzer<'tcx> {
    /// The impl item of std.rs's `Invariant::invariant` at `ty` in `owner_fn_id`'s environment:
    /// `ty`'s invariant, which contracts conjoin. `None` when no impl resolves, and for a type
    /// whose values have one model (a singleton sort), whose invariant is left out.
    pub fn type_invariant_instance(
        &self,
        ty: mir_ty::Ty<'tcx>,
        owner_fn_id: DefId,
    ) -> Option<mir_ty::Instance<'tcx>> {
        use mir_ty::TypeVisitableExt as _;
        let inv_did = self.crate_type_invariant()?;
        if ty.has_escaping_bound_vars() {
            return None;
        }
        let typing_env =
            analyze::predicate_typing_env(self.tcx, owner_fn_id, self.def_ids().model_ty());
        let args = self.tcx.mk_args(&[ty.into()]);
        let instance = mir_ty::Instance::try_resolve(self.tcx, typing_env, inv_did, args)
            .ok()
            .flatten()
            .filter(|instance| instance.def_id() != inv_did)?;
        let singleton = self
            .type_builder(self.def_ids(), owner_fn_id)
            .build(ty)
            .to_sort()
            .is_singleton();
        (!singleton).then_some(instance)
    }

    /// The `invariant` predicate of std.rs's `Invariant`, when an impl of it exists in the crate.
    pub(super) fn crate_type_invariant(&self) -> Option<DefId> {
        let trait_did = self.def_ids().type_invariant()?;
        self.tcx.all_impls(trait_did).next()?;
        invariant_pred(self.tcx, trait_did)
    }

    /// A type with an invariant ([`Self::type_invariant_instance`]) that `roots` hold once
    /// normalized (which reveals opaque types): one of them, or a type among their generic
    /// arguments, references, tuples, arrays, slices, function pointers, and the signatures of
    /// function items and closures, whose results reach a trait method through
    /// `FnOnce::Output`. A closure's captures and an ADT's fields are not looked into.
    fn invariant_type_in(
        &self,
        roots: impl IntoIterator<Item = mir_ty::Ty<'tcx>>,
        owner_fn_id: DefId,
    ) -> Option<mir_ty::Ty<'tcx>> {
        let tcx = self.tcx;
        self.crate_type_invariant()?;
        let typing_env = analyze::predicate_typing_env(tcx, owner_fn_id, self.def_ids().model_ty());
        let normalize = |ty: mir_ty::Ty<'tcx>| {
            let ty = tcx.erase_regions(ty);
            tcx.try_normalize_erasing_regions(typing_env, ty)
                .unwrap_or(ty)
        };
        let mut pending: Vec<_> = roots.into_iter().map(normalize).collect();
        let mut seen = HashSet::new();
        while let Some(root) = pending.pop() {
            let mut walker = root.walk();
            while let Some(arg) = walker.next() {
                let Some(ty) = arg.as_type() else {
                    continue;
                };
                if !seen.insert(ty) {
                    walker.skip_current_subtree();
                    continue;
                }
                if self.type_invariant_instance(ty, owner_fn_id).is_some() {
                    return Some(ty);
                }
                match ty.kind() {
                    mir_ty::TyKind::Closure(_, closure_args) => {
                        walker.skip_current_subtree();
                        let closure = closure_args.as_closure();
                        pending.extend(closure.parent_args().iter().filter_map(|a| a.as_type()));
                        pending.push(normalize(closure.sig_as_fn_ptr_ty()));
                    }
                    mir_ty::TyKind::FnDef(def_id, fn_args) => {
                        let sig = tcx.fn_sig(*def_id).instantiate(tcx, fn_args);
                        let sig = tcx.instantiate_bound_regions_with_erased(sig);
                        pending.extend(sig.inputs_and_output.iter().map(normalize));
                    }
                    _ => {}
                }
            }
        }
        None
    }

    /// Stops when the contract of `local_def_id` (the def `def_id`'s contract comes from) at
    /// `generic_args`, used by `caller_def_id` without a body analyzed there (std code, a trusted
    /// function, a derived method), promises a type's invariant: of its result, or of a `&mut`
    /// parameter's final value. The contract was established over type parameters, where it has
    /// no such conjunct.
    pub fn stop_promised_invariant(
        &mut self,
        def_id: DefId,
        local_def_id: rustc_span::def_id::LocalDefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) {
        if self.crate_type_invariant().is_none()
            || generic_args.types().next().is_none()
            || self.is_derived_clone(def_id)
        {
            return;
        }
        let promised = {
            let mut analyzer = self.local_def_analyzer(local_def_id);
            analyzer
                .owner_fn_id(caller_def_id)
                .generic_args(generic_args);
            analyzer.invariant_in_contract(false)
        };
        let Some(ty) = promised else {
            return;
        };
        self.tcx.dcx().fatal(format!(
            "`{}`, which Thrust does not analyze, would promise the invariant of `{ty}` in `{}`; \
             its contract was written over type parameters, which have none: use it at types \
             without one, or through a function of the crate whose contract states what it keeps",
            self.tcx.def_path_str_with_args(def_id, generic_args),
            self.tcx.def_path_str(caller_def_id),
        ))
    }

    /// Whether `def_id` is the `clone` of a derived `Clone`, which keeps the invariant: its
    /// contract makes the result's model that of `*self`, whose invariant it requires.
    pub(super) fn is_derived_clone(&self, def_id: DefId) -> bool {
        let Some(impl_def_id) = self.tcx.impl_of_assoc(def_id) else {
            return false;
        };
        self.tcx.is_automatically_derived(impl_def_id)
            && self.tcx.trait_id_of_impl(impl_def_id) == self.tcx.lang_items().clone_trait()
    }

    /// Stops when code Thrust does not analyze runs crate code that relies on a type's invariant
    /// nobody checked there: a function whose contract requires the invariant (std's
    /// `Option::<C>::clone` running `C::clone`, a derived `PartialEq` of a struct running its field's
    /// `eq`, a trusted function calling one), or a generic destructor, checked once over its type
    /// parameters, at an instance that holds a type with an invariant (std's `unwrap_or` dropping a
    /// `W<C>`), whose calls at a type parameter run impls that assume it. The walk is the one of
    /// [`Self::stop_ignored_reached`], from the same roots: a body is analyzed when `analyzed`
    /// says so of its def and, for a generic def, when it was analyzed at that instance; drop glue or a shim that forwards a call (to a function pointer, a
    /// closure, a vtable entry) runs its callees on behalf of whoever entered it. The `clone` of a
    /// tuple or an array is a shim that Thrust does not analyze.
    pub fn stop_invariant_assumed_unanalyzed(
        &mut self,
        roots: Vec<mir_ty::Instance<'tcx>>,
        generic_roots: Vec<DefId>,
        analyzed: impl Fn(DefId) -> bool,
    ) {
        if self.crate_type_invariant().is_none() {
            return;
        }
        let analyzed_at = self.analyzed_instance_set();
        type Node<'tcx> = (mir_ty::Instance<'tcx>, bool);
        let mut parent: HashMap<Node<'tcx>, Option<Node<'tcx>>> = HashMap::new();
        let mut pending = std::collections::VecDeque::new();
        for root in self.walk_roots(roots, generic_roots, |_| true) {
            let node = (root, false);
            if parent.insert(node, None).is_none() {
                pending.push_back(node);
            }
        }
        while let Some(node @ (instance, entered_unanalyzed)) = pending.pop_front() {
            if entered_unanalyzed {
                if let Some(message) = self.assumed_invariant(instance) {
                    self.stop_with_path(instance, &message, node, &parent);
                }
            }
            if !self.runs_body(instance) {
                continue;
            }
            let body_unanalyzed = match instance.def {
                mir_ty::InstanceKind::Item(def_id) => {
                    !analyzed(def_id)
                        || (self.is_generic(instance) && !analyzed_at.contains(&instance))
                }
                _ if forwards(instance) => entered_unanalyzed,
                _ => true,
            };
            for callee in self.callees(instance) {
                let next = (callee, body_unanalyzed);
                if let std::collections::hash_map::Entry::Vacant(entry) = parent.entry(next) {
                    entry.insert(Some(node));
                    pending.push_back(next);
                }
            }
        }
    }

    /// The instances of generic defs whose bodies were analyzed at concrete arguments. A
    /// generic body verified over its type parameters lacks the invariant's conjuncts there, so
    /// at another instance it counts as not analyzed.
    fn analyzed_instance_set(&self) -> HashSet<mir_ty::Instance<'tcx>> {
        use mir_ty::TypeVisitableExt as _;
        let typing_env = mir_ty::TypingEnv::fully_monomorphized();
        self.analyzed_instances
            .borrow()
            .iter()
            .filter(|(_, args)| !args.has_param())
            .filter_map(|&(def_id, args)| {
                let args = analyze::body_args(self.tcx, def_id, args);
                mir_ty::Instance::try_resolve(self.tcx, typing_env, def_id, args)
                    .ok()
                    .flatten()
            })
            .collect()
    }

    /// What `instance`, a function of the crate, relies on of a type's invariant when code Thrust
    /// does not analyze runs it, as the error to report.
    fn assumed_invariant(&mut self, instance: mir_ty::Instance<'tcx>) -> Option<String> {
        let mir_ty::InstanceKind::Item(def_id) = instance.def else {
            return None;
        };
        let local_def_id = def_id.as_local()?;
        if !self.tcx.def_kind(def_id).is_fn_like() || self.tcx.is_closure_like(def_id) {
            return None;
        }
        if is_destructor(self.tcx, def_id) {
            let ty = self.invariant_type_in(instance.args.types(), def_id)?;
            return Some(format!(
                "the destructor `{instance}` is checked once over its type parameters, and here it \
                 runs at `{ty}`, which has an invariant that the impls it calls may assume"
            ));
        }
        let ty = {
            let mut analyzer = self.local_def_analyzer(local_def_id);
            analyzer.generic_args(instance.args);
            analyzer.invariant_in_contract(true)
        }?;
        Some(format!("`{instance}` assumes the invariant of `{ty}`"))
    }

    fn stop_with_path(
        &self,
        instance: mir_ty::Instance<'tcx>,
        message: &str,
        node: (mir_ty::Instance<'tcx>, bool),
        parent: &HashMap<(mir_ty::Instance<'tcx>, bool), Option<(mir_ty::Instance<'tcx>, bool)>>,
    ) -> ! {
        let mut path = Vec::new();
        let mut cursor = Some(node);
        while let Some(current) = cursor {
            path.push(current);
            cursor = parent.get(&current).copied().flatten();
        }
        path.reverse();
        let caller = path
            .iter()
            .rev()
            .skip(1)
            .find(|(instance, _)| !forwards(*instance))
            .map(|(instance, _)| instance.to_string())
            .unwrap_or_default();
        let path: Vec<_> = path
            .iter()
            .map(|(instance, _)| instance.to_string())
            .collect();
        self.tcx
            .dcx()
            .struct_span_fatal(
                self.tcx.def_span(instance.def_id()),
                format!(
                    "{message}, but `{caller}`, which Thrust does not analyze, runs it, so nothing \
                     checks the invariant there"
                ),
            )
            .with_note(format!("reached through {}", path.join(" -> ")))
            .emit()
    }
}

/// Whether `instance` is drop glue or a shim that forwards a call (to a function pointer, a
/// closure, a vtable entry), which runs its callees on behalf of whoever entered it.
fn forwards(instance: mir_ty::Instance<'_>) -> bool {
    matches!(
        instance.def,
        mir_ty::InstanceKind::DropGlue(..)
            | mir_ty::InstanceKind::FnPtrShim(..)
            | mir_ty::InstanceKind::ReifyShim(..)
            | mir_ty::InstanceKind::ClosureOnceShim { .. }
            | mir_ty::InstanceKind::VTableShim(..)
    )
}

fn is_destructor(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.impl_of_assoc(def_id).is_some_and(|impl_def_id| {
        tcx.trait_id_of_impl(impl_def_id) == tcx.lang_items().drop_trait()
    })
}

fn invariant_pred(tcx: TyCtxt<'_>, trait_did: DefId) -> Option<DefId> {
    Some(
        tcx.associated_items(trait_did)
            .filter_by_name_unhygienic(rustc_span::Symbol::intern("invariant"))
            .next()?
            .def_id,
    )
}
