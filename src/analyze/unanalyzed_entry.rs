//! Items whose contract Thrust infers, entered from code Thrust does not analyze.
//!
//! The precondition of an item without a written contract is inferred from the calls Thrust
//! analyzes. Code Thrust does not analyze (a trusted body, a function outside
//! `THRUST_VERIFY_ONLY` trusted for its contract, std code) may run such an item too, and its
//! calls add nothing to that precondition. At each such entry the precondition is fixed instead,
//! as Creusot, Verus, Prusti and Dafny fix an omitted `requires` and Flux an unrefined `Fn` bound:
//! to the `pre!` the entering contract states of the item, and otherwise to `true` for every
//! argument.
//!
//! - A function or method run by name or through a bound has only its parameters as state; its
//!   entry is an edge of the walk below, answered by a clause that its precondition holds of every
//!   argument ([`Analyzer::accepts_every_argument`]), unless the analyzed call that led into the
//!   unanalyzed code on its path discharged a `requires` stating its `pre!` at the callee's
//!   generic arguments, and no crate function with its own contract lies between that call and
//!   the entry, nor a closure written outside the callee whose `requires` states it.
//! - A closure is handed over as a value, with captures the walk does not see. Its obligation is
//!   stated at the analyzed call that hands it over (`basic_block::closure_escape`), which records
//!   the hand-over; an entry the walk finds into a closure on a path where the analyzed call
//!   that led into unanalyzed code did not hand it over stops, whatever other calls hand over.
//!   That call states the obligation of the values of the closure's type it finds in its
//!   arguments, or takes the `pre!` its callee's `requires` states of one; at a generic caller
//!   a type parameter may stand for a type holding more, so the walk counts the values again
//!   on the argument types of each instance of the caller ([`HandoverCount`]), and an instance
//!   holding more, or holding them some way the count does not see through, stops.
//! - std's `impl Fn* for &F` forwards a call to `F`, so the walk takes the analyzed-ness of the
//!   instance it is reached from, as a closure call shim does: the call is typed through the
//!   contract of `F`, and the instance a function item or closure runs from it is not an entry.

use std::collections::{HashSet, VecDeque};

use rustc_middle::ty::{self as mir_ty};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::analyze;
use crate::chc;
use crate::rty;

/// What an analyzed call into code Thrust does not analyze covers: a closure it hands over, with
/// its obligation or with the `pre!` the callee's `requires` states of it, which the call
/// discharges, or a function whose `pre!` that `requires` states.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HandedOver<'tcx> {
    /// The closure itself.
    Closure(DefId),
    /// Whatever closure the body's type parameter (by its def id) is instantiated with.
    Param(DefId),
    /// A function or trait method at generic arguments, as the `requires` names it.
    Function(DefId, mir_ty::GenericArgsRef<'tcx>),
}

/// What a `requires` reads the precondition of with `pre!`, as its translation records it
/// ([`analyze::annot_fn::FormulaFn::pre_receivers`]): directly or in the body of a predicate it
/// calls, at the contract's generic arguments.
#[derive(Debug, Clone, Default)]
pub struct StatedPres<'tcx> {
    receivers: Vec<mir_ty::Ty<'tcx>>,
}

impl<'tcx> StatedPres<'tcx> {
    /// Whether the `requires` reads the precondition of the closure or type parameter `ty`.
    pub fn names(&self, ty: mir_ty::Ty<'tcx>) -> bool {
        self.receivers.contains(&ty)
    }

    /// The functions whose precondition the `requires` reads, with their generic arguments.
    pub fn functions(&self) -> Vec<(DefId, mir_ty::GenericArgsRef<'tcx>)> {
        self.receivers
            .iter()
            .filter_map(|ty| match *ty.kind() {
                mir_ty::TyKind::FnDef(def_id, args) => Some((def_id, args)),
                _ => None,
            })
            .collect()
    }
}

/// How many values of the closure type a closure parameter of an unanalyzed callee is
/// instantiated with an analyzed call states the obligation of, as the analysis of its caller
/// found them at the caller's generic types.
#[derive(Debug, Clone)]
pub struct HandoverCount<'tcx> {
    /// The analyzed body that makes the call.
    pub owner: DefId,
    /// The function called, with its generic arguments.
    pub callee: DefId,
    pub callee_args: mir_ty::GenericArgsRef<'tcx>,
    /// The type the callee's closure parameter is instantiated with.
    pub ty: mir_ty::Ty<'tcx>,
    /// The types of the call's arguments.
    pub operand_types: Vec<mir_ty::Ty<'tcx>>,
    /// The values of `ty` the call states the obligation of, one by one or by the `pre!` the
    /// callee's `requires` states; for a closure held by an `IteratorSpec` argument, whose
    /// `inv` states it, `0`, and `operand_types` are the other arguments.
    pub accounted: usize,
    pub span: rustc_span::Span,
}

/// An instance at which a call hands over values of a closure type its analysis does not
/// account for: the instance of the caller, the closure type, and how many values its
/// arguments hold, `None` when some are held a way the count does not see through.
#[derive(Debug, Clone)]
pub struct Miscounted<'tcx> {
    pub count: HandoverCount<'tcx>,
    pub owner: mir_ty::Instance<'tcx>,
    pub closure: mir_ty::Ty<'tcx>,
    pub held: Option<usize>,
}

/// The entries of the walk from code Thrust does not analyze into crate items it analyzes.
#[derive(Debug, Default)]
pub struct Entries<'tcx> {
    /// Functions and methods, with the unanalyzed instance each is entered from.
    pub items: Vec<(mir_ty::Instance<'tcx>, mir_ty::Instance<'tcx>)>,
    /// Closures entered on a path on which no analyzed call handed them over, likewise.
    pub unhanded_closures: Vec<(mir_ty::Instance<'tcx>, mir_ty::Instance<'tcx>)>,
    /// The closure and function pointer types an entered function returns, or can store
    /// behind a `&mut` argument, to the unanalyzed instance it is entered from: values the
    /// walk does not see handed over.
    pub escaping: Vec<(
        mir_ty::Instance<'tcx>,
        mir_ty::Instance<'tcx>,
        mir_ty::Ty<'tcx>,
    )>,
    /// The calls that hand over, at an instance of their caller, values of a closure type they
    /// do not state the obligation of ([`Analyzer::miscounted_at`]).
    pub miscounted: Vec<Miscounted<'tcx>>,
}

/// An instance on the walk: whether its body is analyzed, and, for one that is not, what the
/// analyzed call that led into unanalyzed code on its path covers there.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Node<'tcx> {
    instance: mir_ty::Instance<'tcx>,
    analyzed: bool,
    covered: Covered<'tcx>,
}

/// What an analyzed call into unanalyzed code covers ([`HandedOver`]), resolved at the instance
/// of the caller.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
struct Covered<'tcx> {
    /// The closures handed over, sorted by [`def_order`], without repeats.
    closures: Vec<DefId>,
    /// The function instances whose `pre!` the callee's `requires` states, sorted by
    /// [`fn_order`], without repeats.
    functions: Vec<mir_ty::Instance<'tcx>>,
    /// The crate function whose contract states `functions`: the closures written in its body
    /// are its code and stay covered, other closures are not. `None` when `functions` is empty.
    stated_in: Option<DefId>,
}

impl<'tcx> analyze::Analyzer<'tcx> {
    /// Records the fn-like defs whose bodies are trusted rather than analyzed.
    pub fn set_trusted_bodies(&mut self, trusted: HashSet<LocalDefId>) {
        self.trusted_bodies = trusted;
    }

    /// Whether `def_id` is a crate function whose body is trusted rather than analyzed.
    pub fn is_trusted_body(&self, def_id: DefId) -> bool {
        def_id
            .as_local()
            .is_some_and(|local| self.trusted_bodies.contains(&local))
    }

    /// Whether `def_id` is a crate function with a written `requires`.
    pub fn has_written_requires(&self, def_id: DefId) -> bool {
        def_id.as_local().is_some_and(|local| {
            self.extract_path_with_attr(local, &analyze::annot::requires_path_path())
                .is_some()
        })
    }

    /// Records that the analyzed body `owner` hands `handed_over` to `callee` at `callee_args`
    /// at a call.
    pub fn record_handover(
        &mut self,
        owner: DefId,
        callee: DefId,
        callee_args: mir_ty::GenericArgsRef<'tcx>,
        handed_over: HandedOver<'tcx>,
    ) {
        self.handovers
            .push((owner, callee, callee_args, handed_over));
    }

    /// Records how many values of a closure type an analyzed call states the obligation of.
    pub fn record_handover_count(&mut self, count: HandoverCount<'tcx>) {
        self.handover_counts.push(count);
    }

    /// What the `requires` of `contract_def_id` at `contract_args` reads the precondition of,
    /// translated for `owner_fn_id`.
    pub fn stated_pres(
        &self,
        contract_def_id: DefId,
        contract_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> StatedPres<'tcx> {
        let formula_fn = contract_def_id
            .as_local()
            .and_then(|local| {
                self.extract_path_with_attr(local, &analyze::annot::requires_path_path())
            })
            .and_then(DefId::as_local)
            .and_then(|formula_def_id| {
                self.formula_fn_with_args(formula_def_id, contract_args, owner_fn_id)
            });
        // A precondition the `requires` reads in a position other than only positive ones is
        // not fixed by it: the solver may choose it smaller than the real one. A closure with a
        // written contract has no such unknown, and its precondition is the written one.
        let receivers = formula_fn
            .map(|formula_fn| {
                let written =
                    formula_fn
                        .mixed_pre_receivers()
                        .into_iter()
                        .filter(|ty| match *ty.kind() {
                            mir_ty::TyKind::Closure(def_id, _) => self.has_written_requires(def_id),
                            _ => false,
                        });
                formula_fn
                    .pre_receivers()
                    .into_iter()
                    .chain(written)
                    .collect()
            })
            .unwrap_or_default();
        StatedPres { receivers }
    }

    /// The contract a call of `def_id` at `args` from an analyzed body is checked against when
    /// the function that runs is not analyzed, with that contract's generic arguments: a
    /// trusted crate function's, or the extern spec of a std function. `None` when the function
    /// is analyzed, or has no such contract.
    pub fn unanalyzed_contract(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
    ) -> Option<(DefId, mir_ty::GenericArgsRef<'tcx>)> {
        let analyzed = def_id.is_local()
            && (!self.is_trusted_body(def_id) || self.tcx.is_closure_like(def_id));
        if analyzed {
            return None;
        }
        self.contract_of(def_id, args)
    }

    /// The contract a call of `def_id` at `args` is checked against when it resolves to
    /// `resolved_def_id`, if that is the trait method's ([`analyze::Analyzer::takes_trait_contract`]).
    /// `None` when the call takes the impl method's own.
    pub fn inherited_contract(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        resolved_def_id: DefId,
    ) -> Option<(DefId, mir_ty::GenericArgsRef<'tcx>)> {
        if !self.takes_trait_contract(def_id, resolved_def_id) {
            return None;
        }
        self.contract_of(def_id, args)
    }

    /// The def whose annotations give `def_id` its contract at `args`, with its generic
    /// arguments: `def_id` itself, or the extern-spec wrapper that carries the contract of a std
    /// function or of a trusted generic one.
    fn contract_of(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
    ) -> Option<(DefId, mir_ty::GenericArgsRef<'tcx>)> {
        let specs = match self.defs.get(&def_id)? {
            analyze::DefTy::Concrete(_, spec) => {
                let spec = spec.map_or(def_id, |spec| spec.to_def_id());
                return Some((spec, args));
            }
            analyze::DefTy::Deferred(specs) => specs,
            analyze::DefTy::Generic(_) => return Some((def_id, args)),
        };
        specs.iter().find_map(|spec| {
            let spec_def_id = spec.local_def_id.to_def_id();
            let Some(target_args) = spec.target_args else {
                return Some((spec_def_id, args));
            };
            let bound = analyze::extern_spec::bind_spec_args(
                self.tcx,
                spec.local_def_id,
                target_args,
                args,
            )?;
            Some((spec_def_id, bound))
        })
    }

    /// Walks the instances the verified functions can run, as
    /// [`analyze::Analyzer::stop_ignored_reached`] does from `roots`, and returns the
    /// edges from an instance whose body Thrust does not analyze into a crate function it
    /// analyzes: a closure, or a function or method that the analyzed call leading into the
    /// unanalyzed code on its path does not cover ([`HandedOver::Function`]). A non-local
    /// instance is not analyzed; a closure call shim takes the analyzed-ness of the instance it
    /// is reached from, since a call Thrust types through the closure's contract goes through
    /// it, and so does std's `impl Fn for &F`, which forwards the call to `F`; other shims are
    /// not analyzed. The entry function is left out: its precondition is
    /// required of every argument already (`crate_::Analyzer::assert_callable_entry`).
    ///
    /// `fallback_roots` are the trusted functions of the crate: each is entered from the analyzed
    /// calls that lead into it, and is walked as a root, with nothing covered, only when the walk
    /// from `roots` reached none of its instances.
    pub fn unanalyzed_entries(
        &self,
        roots: Vec<mir_ty::Instance<'tcx>>,
        fallback_roots: Vec<mir_ty::Instance<'tcx>>,
        is_analyzed: impl Fn(DefId) -> bool,
    ) -> Entries<'tcx> {
        let entry_fn = self.tcx.entry_fn(()).map(|(def_id, _)| def_id);
        let item_analyzed = |instance: mir_ty::Instance<'tcx>| match instance.def {
            mir_ty::InstanceKind::Item(def_id) => def_id.is_local() && is_analyzed(def_id),
            _ => false,
        };
        let mut seen = HashSet::new();
        let mut entries = Entries::default();
        self.walk_entries(roots, &item_analyzed, entry_fn, &mut seen, &mut entries);
        // A fallback root that no walk reached is reached by no analyzed call, so nothing is
        // covered there. One reached has been walked with what its callers cover.
        let reached: HashSet<_> = seen.iter().map(|node| node.instance).collect();
        let unreached = fallback_roots
            .into_iter()
            .filter(|root| !reached.contains(root))
            .collect();
        self.walk_entries(unreached, &item_analyzed, entry_fn, &mut seen, &mut entries);
        entries
    }

    /// Continues the walk of [`Self::unanalyzed_entries`] from `roots`, which start with nothing
    /// covered, over the nodes `seen`.
    fn walk_entries(
        &self,
        roots: Vec<mir_ty::Instance<'tcx>>,
        item_analyzed: &impl Fn(mir_ty::Instance<'tcx>) -> bool,
        entry_fn: Option<DefId>,
        seen: &mut HashSet<Node<'tcx>>,
        entries: &mut Entries<'tcx>,
    ) {
        let mut pending = VecDeque::new();
        for root in roots {
            let node = Node {
                instance: root,
                analyzed: item_analyzed(root),
                covered: Covered::default(),
            };
            if seen.insert(node.clone()) {
                pending.push_back(node);
            }
        }
        while let Some(node) = pending.pop_front() {
            let instance = node.instance;
            if !self.runs_body(instance) || self.nests_past_recursion_limit(instance) {
                continue;
            }
            for callee in self.callees(instance) {
                let analyzed = match callee.def {
                    mir_ty::InstanceKind::ClosureOnceShim { .. }
                    | mir_ty::InstanceKind::FnPtrShim(..) => node.analyzed,
                    // A call through `&F` is typed through the contract of `F` (`impl Fn for
                    // &F` forwards to it), as a closure call shim is.
                    mir_ty::InstanceKind::Item(def_id) if self.is_shared_ref_fn_impl(def_id) => {
                        node.analyzed
                    }
                    _ => item_analyzed(callee),
                };
                let covered = match (node.analyzed, analyzed) {
                    (_, true) => Covered::default(),
                    (true, false) => {
                        entries
                            .miscounted
                            .extend(self.miscounted_at(instance, callee));
                        self.covered_at(instance, callee)
                    }
                    (false, false) => self.carried_into(&node.covered, callee),
                };
                let child = Node {
                    instance: callee,
                    analyzed,
                    covered,
                };
                if seen.insert(child.clone()) {
                    pending.push_back(child);
                }
                if node.analyzed || !analyzed {
                    continue;
                }
                let callee_def_id = callee.def_id();
                if Some(callee_def_id) == entry_fn {
                    continue;
                }
                entries.escaping.extend(
                    self.escaping_callables(callee)
                        .into_iter()
                        .map(|ty| (callee, instance, ty)),
                );
                if self.tcx.is_closure_like(callee_def_id) {
                    if !node.covered.closures.contains(&callee_def_id) {
                        entries.unhanded_closures.push((callee, instance));
                    }
                } else if !node.covered.functions.iter().any(|f| same_fn(*f, callee)) {
                    entries.items.push((callee, instance));
                }
            }
        }
    }

    /// Whether `def_id` is a method of std's `impl Fn*<A> for &F`, which forwards a call to `F`:
    /// a non-local impl for a shared reference to one of its own type parameters. A crate's own
    /// `impl Fn<A> for &S` runs its own body.
    fn is_shared_ref_fn_impl(&self, def_id: DefId) -> bool {
        let Some(impl_def_id) = self.tcx.impl_of_assoc(def_id) else {
            return false;
        };
        if impl_def_id.is_local() {
            return false;
        }
        let Some(trait_ref) = self.tcx.impl_trait_ref(impl_def_id) else {
            return false;
        };
        let trait_ref = trait_ref.instantiate_identity();
        self.tcx
            .fn_trait_kind_from_def_id(trait_ref.def_id)
            .is_some()
            && matches!(
                trait_ref.self_ty().kind(),
                mir_ty::TyKind::Ref(_, inner, mir_ty::Mutability::Not)
                    if matches!(inner.kind(), mir_ty::TyKind::Param(_))
            )
    }

    /// The closure and function pointer types in what `instance` returns and in the types
    /// behind a `&mut` among its parameters, the fields of structs and enums included.
    fn escaping_callables(&self, instance: mir_ty::Instance<'tcx>) -> Vec<mir_ty::Ty<'tcx>> {
        let typing_env = mir_ty::TypingEnv::fully_monomorphized();
        let fn_ty = instance.ty(self.tcx, typing_env);
        let sig = match fn_ty.kind() {
            mir_ty::TyKind::Closure(_, args) => args.as_closure().sig(),
            mir_ty::TyKind::FnDef(..) => fn_ty.fn_sig(self.tcx),
            _ => return Vec::new(),
        };
        let sig = self.tcx.instantiate_bound_regions_with_erased(sig);
        let sig = self.tcx.normalize_erasing_regions(typing_env, sig);
        let written = sig.inputs().iter().copied().filter(|ty| {
            self.reachable_types(*ty).iter().any(|ty| {
                matches!(
                    ty.kind(),
                    mir_ty::TyKind::Ref(_, _, mir_ty::Mutability::Mut)
                )
            })
        });
        std::iter::once(sig.output())
            .chain(written)
            .flat_map(|ty| self.reachable_types(ty))
            .filter(|ty| {
                matches!(
                    ty.kind(),
                    mir_ty::TyKind::Closure(..) | mir_ty::TyKind::FnPtr(..)
                )
            })
            .collect()
    }

    /// The types a value of `ty` holds: its type arguments and the field types of the structs
    /// and enums in it, transitively. A closure's own arguments (its signature, its captures)
    /// are its own and not followed.
    fn reachable_types(&self, ty: mir_ty::Ty<'tcx>) -> Vec<mir_ty::Ty<'tcx>> {
        let typing_env = mir_ty::TypingEnv::fully_monomorphized();
        let mut seen = HashSet::new();
        let mut pending = vec![ty];
        let mut reached = Vec::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            let mut walker = ty.walk();
            while let Some(arg) = walker.next() {
                let Some(inner) = arg.as_type() else {
                    continue;
                };
                reached.push(inner);
                match inner.kind() {
                    mir_ty::TyKind::Closure(..) => walker.skip_current_subtree(),
                    mir_ty::TyKind::Adt(adt, args) => {
                        pending.extend(adt.all_fields().map(|field| {
                            self.tcx
                                .normalize_erasing_regions(typing_env, field.ty(self.tcx, args))
                        }));
                    }
                    _ => {}
                }
            }
        }
        reached
    }

    /// Whether the generic arguments of `instance` nest as deeply as the recursion limit, as
    /// those of a polymorphically recursive function do. Such an instance is not followed:
    /// rustc's collector stops at it, and so does `check_reused_instances` afterwards.
    fn nests_past_recursion_limit(&self, instance: mir_ty::Instance<'tcx>) -> bool {
        let limit = self.tcx.recursion_limit().0;
        instance
            .args
            .iter()
            .any(|arg| analyze::extern_spec::type_depth(arg) >= limit)
    }

    /// The contract of the function `instance` runs, at its generic arguments, when its
    /// precondition is inferred. A generic def's template tells before its body is analyzed at
    /// the instance.
    pub fn entered_inferred_fn_ty(
        &mut self,
        instance: mir_ty::Instance<'tcx>,
    ) -> Option<rty::FunctionType> {
        let def_id = instance.def_id();
        let template = self
            .concrete_def_ty(def_id)
            .and_then(|def_ty| def_ty.ty.as_function().cloned());
        if template
            .as_ref()
            .is_some_and(|fn_ty| !self.infers_precondition(fn_ty))
        {
            return None;
        }
        let generic = self
            .tcx
            .generics_of(def_id)
            .requires_monomorphization(self.tcx);
        let fn_ty = if generic {
            self.def_ty_with_args(def_id, instance.args, def_id)?
                .ty
                .as_function()
                .cloned()?
        } else {
            template?
        };
        self.infers_precondition(&fn_ty).then_some(fn_ty)
    }

    /// Whether the precondition of `fn_ty` is inferred: a parameter's refinement names an
    /// unknown, directly or through a predicate's definition, a derived predicate among them.
    pub fn infers_precondition(&self, fn_ty: &rty::FunctionType) -> bool {
        fn_ty.params.iter().any(|param| {
            let reach = self.pred_var_reach(param);
            reach.found || reach.undefined || self.may_apply_derived(param)
        })
    }

    /// The clauses that make the precondition of `fn_ty` hold of every argument.
    pub fn accepts_every_argument(fn_ty: &rty::FunctionType) -> Vec<chc::Clause> {
        let expected = fn_ty
            .params
            .iter()
            .map(|param| {
                rty::RefinedType::<rty::Closed>::unrefined(param.ty.clone().strip_refinement())
            })
            .collect();
        analyze::basic_block::relate_param_sub_types(
            fn_ty.params.clone(),
            &expected,
            &mut chc::ClauseBuilder::default(),
            None,
        )
    }

    /// What an unanalyzed instance that `covered` covers covers in `callee`, unanalyzed too: the
    /// same in std code and in a closure written in the function whose contract states the
    /// covered functions. Elsewhere in the crate only the closures go on, whose obligation was
    /// stated where they were handed over: a crate function has its own contract, whose function
    /// `pre!`s no analyzed call discharges, and a closure written in another function (a trusted
    /// callee's, which is not analyzed either) is that function's code, not the stating
    /// function's. `std.rs` states `pre!` only of closure parameters, so the functions reach std
    /// code only from a trusted crate function's own `requires`; that function is trusted for
    /// the std calls its body makes, as for the arguments it passes them.
    fn carried_into(
        &self,
        covered: &Covered<'tcx>,
        callee: mir_ty::Instance<'tcx>,
    ) -> Covered<'tcx> {
        let callee_def_id = callee.def_id();
        let written_in_stating_fn = self.tcx.is_closure_like(callee_def_id)
            && Some(self.tcx.typeck_root_def_id(callee_def_id)) == covered.stated_in;
        if !callee_def_id.is_local() || written_in_stating_fn {
            return covered.clone();
        }
        Covered {
            closures: covered.closures.clone(),
            ..Covered::default()
        }
    }

    /// The instance `def_id` at `args`, recorded in the analyzed body of `owner`, resolves to at
    /// the instance `owner`.
    fn resolve_recorded(
        &self,
        owner: mir_ty::Instance<'tcx>,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
    ) -> Option<mir_ty::Instance<'tcx>> {
        let typing_env = mir_ty::TypingEnv::fully_monomorphized();
        let args = self
            .tcx
            .try_instantiate_and_normalize_erasing_regions(
                owner.args,
                typing_env,
                mir_ty::EarlyBinder::bind(args),
            )
            .ok()?;
        mir_ty::Instance::try_resolve(self.tcx, typing_env, def_id, args)
            .ok()
            .flatten()
    }

    /// What the analyzed instance `owner` covers at its calls that run the instance `callee`:
    /// the closures, by def id, it hands over, and the function instances whose `pre!` those
    /// calls discharge.
    fn covered_at(
        &self,
        owner: mir_ty::Instance<'tcx>,
        callee: mir_ty::Instance<'tcx>,
    ) -> Covered<'tcx> {
        let owner_def_id = owner.def_id();
        let mut covered = Covered::default();
        let recorded = self.handovers.iter().filter(|(o, c, args, _)| {
            *o == owner_def_id
                && self
                    .resolve_recorded(owner, *c, args)
                    .is_some_and(|runs| same_fn(runs, callee))
        });
        for (_, _, _, handed_over) in recorded {
            match *handed_over {
                HandedOver::Closure(def_id) => covered.closures.push(def_id),
                HandedOver::Function(def_id, args) => {
                    covered
                        .functions
                        .extend(self.resolve_recorded(owner, def_id, args));
                }
                HandedOver::Param(param_def_id) => {
                    let generics = self.tcx.generics_of(owner_def_id);
                    let Some(&index) = generics.param_def_id_to_index.get(&param_def_id) else {
                        continue;
                    };
                    let Some(ty) = owner.args.get(index as usize).and_then(|a| a.as_type()) else {
                        continue;
                    };
                    covered.closures.extend(ty.walk().filter_map(|arg| {
                        match arg.as_type().map(|ty| *ty.kind()) {
                            Some(mir_ty::TyKind::Closure(def_id, _)) => Some(def_id),
                            _ => None,
                        }
                    }));
                }
            }
        }
        covered.closures.sort_by_key(|def_id| def_order(*def_id));
        covered.closures.dedup();
        covered.functions.sort_by_key(|f| fn_order(*f));
        covered.functions.dedup_by(|f, g| same_fn(*f, *g));
        if !covered.functions.is_empty() {
            covered.stated_in = Some(callee.def_id());
        }
        covered
    }
}

impl<'tcx> analyze::Analyzer<'tcx> {
    /// The calls of the analyzed instance `owner` that run the instance `callee` and hand it
    /// values of a closure type other than those their analysis states the obligation of,
    /// counted on the argument types at `owner` ([`HandoverCount`]). A value behind references
    /// and boxes counts as one of the closure type, as the coverage records it. Only closures
    /// whose precondition is inferred count: one with a written `requires` is trusted to be
    /// called as it says.
    fn miscounted_at(
        &self,
        owner: mir_ty::Instance<'tcx>,
        callee: mir_ty::Instance<'tcx>,
    ) -> Vec<Miscounted<'tcx>> {
        let owner_def_id = owner.def_id();
        let mut miscounted = Vec::new();
        for count in &self.handover_counts {
            if count.owner != owner_def_id
                || !self
                    .resolve_recorded(owner, count.callee, count.callee_args)
                    .is_some_and(|runs| same_fn(runs, callee))
            {
                continue;
            }
            let Some(ty) = self.instantiate_at(owner, count.ty) else {
                miscounted.push(Miscounted {
                    count: count.clone(),
                    owner,
                    closure: count.ty,
                    held: None,
                });
                continue;
            };
            let closure = peel_refs(ty);
            // Code Thrust does not analyze is trusted to call a closure with a written
            // `requires` as it says, as it is trusted to call one it is not handed.
            let inferred = match *closure.kind() {
                mir_ty::TyKind::Closure(def_id, _) => !self.has_written_requires(def_id),
                _ => false,
            };
            if !inferred {
                continue;
            }
            let held = count
                .operand_types
                .iter()
                .map(|held| {
                    self.instantiate_at(owner, *held)
                        .and_then(|held| count_held(self.tcx, held, closure))
                })
                .sum::<Option<usize>>();
            if held != Some(count.accounted) {
                miscounted.push(Miscounted {
                    count: count.clone(),
                    owner,
                    closure,
                    held,
                });
            }
        }
        miscounted
    }

    /// `ty`, recorded in the analyzed body of `owner`, at the instance `owner`.
    fn instantiate_at(
        &self,
        owner: mir_ty::Instance<'tcx>,
        ty: mir_ty::Ty<'tcx>,
    ) -> Option<mir_ty::Ty<'tcx>> {
        self.tcx
            .try_instantiate_and_normalize_erasing_regions(
                owner.args,
                mir_ty::TypingEnv::fully_monomorphized(),
                mir_ty::EarlyBinder::bind(ty),
            )
            .ok()
    }
}

/// `ty` without the references and boxes around it.
pub fn peel_refs(ty: mir_ty::Ty<'_>) -> mir_ty::Ty<'_> {
    let mut ty = ty;
    while let Some(inner) = pointee(ty) {
        ty = inner;
    }
    ty
}

/// What `ty` points to, if it is a reference or a box.
pub fn pointee(ty: mir_ty::Ty<'_>) -> Option<mir_ty::Ty<'_>> {
    match ty.kind() {
        mir_ty::TyKind::Ref(_, inner, _) => Some(*inner),
        mir_ty::TyKind::Adt(adt, args) if adt.is_box() => Some(args.type_at(0)),
        _ => None,
    }
}

/// The number of values of type `ty` a value of `held` holds, itself, behind references and
/// boxes, or in the fields of structs and tuples; `None` when it may hold one some other way: in
/// a collection, an enum, a closure's captures, a raw pointer or a `PhantomData`, through an
/// alias, or through a type that holds itself. A type that does not mention `ty` holds none of
/// it; at a generic caller that is a count for the generic types only, which a type parameter
/// may replace with a type holding more ([`HandoverCount`]).
pub fn count_held<'tcx>(
    tcx: mir_ty::TyCtxt<'tcx>,
    held: mir_ty::Ty<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> Option<usize> {
    count_held_within(tcx, held, ty, &mut Vec::new())
}

/// [`count_held`] inside the types `visiting`.
fn count_held_within<'tcx>(
    tcx: mir_ty::TyCtxt<'tcx>,
    held: mir_ty::Ty<'tcx>,
    ty: mir_ty::Ty<'tcx>,
    visiting: &mut Vec<mir_ty::Ty<'tcx>>,
) -> Option<usize> {
    if held == ty {
        return Some(1);
    }
    if !held.walk().any(|arg| arg.as_type() == Some(ty)) {
        return Some(0);
    }
    if visiting.contains(&held) {
        return None;
    }
    visiting.push(held);
    let count = count_held_inside(tcx, held, ty, visiting);
    visiting.pop();
    count
}

/// [`count_held`] of `held`, which mentions `ty`, through its pointee or its fields.
fn count_held_inside<'tcx>(
    tcx: mir_ty::TyCtxt<'tcx>,
    held: mir_ty::Ty<'tcx>,
    ty: mir_ty::Ty<'tcx>,
    visiting: &mut Vec<mir_ty::Ty<'tcx>>,
) -> Option<usize> {
    if let Some(inner) = pointee(held) {
        return count_held_within(tcx, inner, ty, visiting);
    }
    match *held.kind() {
        mir_ty::TyKind::Tuple(elems) => elems
            .iter()
            .map(|elem| count_held_within(tcx, elem, ty, visiting))
            .sum(),
        // A `PhantomData` names a type without holding it, as a collection marks the elements it
        // holds behind a raw allocation (`Vec<T>` holds a `PhantomData<T>`).
        mir_ty::TyKind::Adt(adt, _) if adt.is_phantom_data() => None,
        mir_ty::TyKind::Adt(adt, args) if adt.is_struct() => adt
            .all_fields()
            .map(|field| {
                let field_ty = tcx.erase_regions(field.ty(tcx, args));
                count_held_within(tcx, field_ty, ty, visiting)
            })
            .sum(),
        _ => None,
    }
}

/// Whether two instances have the same def id and generic arguments: the same function, reified
/// or not. A `FnPtrShim` or `ClosureOnceShim` has the def id of the trait method it implements,
/// so it is not the same as the function or closure it calls.
fn same_fn<'tcx>(a: mir_ty::Instance<'tcx>, b: mir_ty::Instance<'tcx>) -> bool {
    a.def_id() == b.def_id() && a.args == b.args
}

/// An order of instances within one compilation that puts those [`same_fn`] identifies next
/// to each other. Generic arguments are interned, so their address identifies them.
fn fn_order(instance: mir_ty::Instance<'_>) -> ((u32, u32), usize) {
    (
        def_order(instance.def_id()),
        instance.args.as_ptr() as usize,
    )
}

/// An order of def ids within one compilation.
fn def_order(def_id: DefId) -> (u32, u32) {
    (def_id.krate.as_u32(), def_id.index.as_u32())
}
