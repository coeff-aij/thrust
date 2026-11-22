//! Retrieves and caches well-known [`DefId`]s.

use std::cell::OnceCell;
use std::rc::Rc;

use rustc_abi::FieldIdx;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use rustc_span::symbol::Symbol;

/// The marker a loop-invariant form of `thrust_macros` calls.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InvariantMarker {
    /// `invariant!`: the whole invariant of its loop head.
    Full,
    /// `partial_invariant!`: conjoined with the predicate inferred at its loop head.
    Partial,
    /// The history of a `for` loop that has no written invariant (`thrust-macros/src/for_loop.rs`):
    /// conjoined as `Partial` is, with the names its formula reads resolved in the marker's scope.
    ForLoopHistory,
}

/// The definitions of the `#[thrust::def::..]` items of std.rs (the model, sequence, logic and marker
/// library), each found once by its attribute: `$name` is the accessor, `$path` the attribute's
/// path from [`crate::analyze::annot`].
macro_rules! annotated_defs {
    ($($(#[$doc:meta])* $name:ident => $path:ident;)*) => {
        #[derive(Debug, Clone, Default)]
        struct AnnotatedDefIds {
            $($name: OnceCell<Option<DefId>>,)*
        }

        impl DefIdCache<'_> {
            $(
                $(#[$doc])*
                pub fn $name(&self) -> Option<DefId> {
                    *self.def_ids.annotated.$name.get_or_init(|| {
                        self.annotated_def(&crate::analyze::annot::$path())
                    })
                }
            )*
        }
    };
}

annotated_defs! {
    model_ty => model_ty_path;
    int_model => int_model_path;
    uint_model => uint_model_path;
    int_n_model => int_n_model_path;
    uint_n_model => uint_n_model_path;
    bit_vec_model => bit_vec_model_path;
    bit_vec_from_int => bit_vec_from_int_path;
    bit_vec_to_int => bit_vec_to_int_path;
    mut_model => mut_model_path;
    box_model => box_model_path;
    array_model => array_model_path;
    closure_model => closure_model_path;
    dyn_model => dyn_model_path;
    ghost_model => ghost_model_path;
    /// The `IteratorSpec` trait of std.rs.
    iterator_spec => iterator_spec_path;
    /// The `PartialOrdSpec` trait of std.rs.
    partial_ord_spec => partial_ord_spec_path;
    /// The `Invariant` trait of std.rs: a type's invariant.
    type_invariant => type_invariant_path;
    mut_model_new => mut_model_new_path;
    box_model_new => box_model_new_path;
    array_model_from_fn => array_model_from_fn_path;
    array_model_store => array_model_store_path;
    seq_model => seq_model_path;
    seq_empty => seq_empty_path;
    seq_singleton => seq_singleton_path;
    int_to_int_n => int_to_int_n_path;
    proof_branch => proof_branch_path;
    int_lit => int_lit_path;
    int_n_to_int => int_n_to_int_path;
    uint_to_uint_n => uint_to_uint_n_path;
    uint_n_to_uint => uint_n_to_uint_path;
    seq_len => seq_len_path;
    seq_push => seq_push_path;
    seq_store => seq_store_path;
    seq_subsequence => seq_subsequence_path;
    seq_concat => seq_concat_path;
    exists => exists_path;
    forall => forall_path;
    implies => implies_path;
    log_eq_args => log_eq_args_path;
    invariant_marker => invariant_marker_path;
    partial_invariant_marker => partial_invariant_marker_path;
    for_loop_history_marker => for_loop_history_marker_path;
    /// The formula `for_loop_history_marker` conjoins.
    for_loop_history => for_loop_history_path;
    /// The ghosts of a `for` loop whose body starts with no invariant: each marker is typed as a
    /// `ghost!` whose term is the formula after it.
    for_loop_iter_old_marker => for_loop_iter_old_marker_path;
    for_loop_iter_old => for_loop_iter_old_path;
    for_loop_produced_marker => for_loop_produced_marker_path;
    for_loop_produced => for_loop_produced_path;
    for_loop_produced_push_marker => for_loop_produced_push_marker_path;
    for_loop_produced_push => for_loop_produced_push_path;
    ghost_marker => ghost_marker_path;
    choose_marker => choose_marker_path;
    witness => witness_path;
    assert_marker => assert_marker_path;
    assume_marker => assume_marker_path;
    block_requires_marker => block_requires_marker_path;
    block_ensures_marker => block_ensures_marker_path;
    fn_param_wrapper => fn_param_wrapper_path;
    fn_param_at_entry => fn_param_at_entry_path;
    closure_precondition => closure_precondition_path;
    closure_postcondition => closure_postcondition_path;
    closure_hist_inv => closure_hist_inv_path;
}

#[derive(Debug, Clone, Default)]
struct DefIds {
    annotated: AnnotatedDefIds,
    unique: OnceCell<Option<DefId>>,
    nonnull: OnceCell<Option<DefId>>,
    slice_iter: OnceCell<Option<DefId>>,
    slice_iter_mut: OnceCell<Option<DefId>>,
    vec_into_iter: OnceCell<Option<DefId>>,
}

/// Retrieves and caches well-known [`DefId`]s.
///
/// [`DefId`]s of some well-known types can be retrieved as lang items or via the definition of
/// lang items. This struct implements that logic and caches the results.
#[derive(Clone)]
pub struct DefIdCache<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_ids: Rc<DefIds>,
}

impl<'tcx> DefIdCache<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            def_ids: Rc::new(DefIds::default()),
        }
    }

    pub fn box_(&self) -> Option<DefId> {
        self.tcx.lang_items().owned_box()
    }

    pub fn vec(&self) -> Option<DefId> {
        self.tcx.get_diagnostic_item(Symbol::intern("Vec"))
    }

    pub fn box_new(&self) -> Option<DefId> {
        self.tcx.get_diagnostic_item(rustc_span::sym::box_new)
    }

    pub fn unique(&self) -> Option<DefId> {
        *self.def_ids.unique.get_or_init(|| {
            let box_did = self.box_()?;
            let box_first_did =
                self.tcx.adt_def(box_did).non_enum_variant().fields[FieldIdx::from_u32(0)].did;
            let unique_def = self
                .tcx
                .type_of(box_first_did)
                .instantiate_identity()
                .ty_adt_def()
                .expect("expected Box to contain Unique");
            Some(unique_def.did())
        })
    }

    pub fn nonnull(&self) -> Option<DefId> {
        *self.def_ids.nonnull.get_or_init(|| {
            let unique_did = self.unique()?;
            let unique_first_did =
                self.tcx.adt_def(unique_did).non_enum_variant().fields[FieldIdx::from_u32(0)].did;
            let nonnull_def = self
                .tcx
                .type_of(unique_first_did)
                .instantiate_identity()
                .ty_adt_def()
                .expect("expected Unique to contain NonNull");
            Some(nonnull_def.did())
        })
    }

    /// The sibling of `anchor` named `name` in the module that defines it.
    ///
    /// `Vec` and `slice::Iter` are the only two of the sequence types with a diagnostic item.
    /// The rest are reached the way `unique` and `nonnull` reach theirs: by walking from an
    /// anchor that is addressable to the one that is not. Here the walk is sideways, from a
    /// type to the module it is declared in, rather than through a field.
    fn sibling_of(&self, anchor: DefId, name: &str) -> Option<DefId> {
        let module = self.tcx.parent(anchor);
        let name = Symbol::intern(name);
        self.tcx
            .module_children(module)
            .iter()
            .find(|child| child.ident.name == name)
            .and_then(|child| child.res.opt_def_id())
    }

    /// `core::slice::Iter`, the iterator `<[T]>::iter` returns.
    pub fn slice_iter(&self) -> Option<DefId> {
        *self
            .def_ids
            .slice_iter
            .get_or_init(|| self.tcx.get_diagnostic_item(Symbol::intern("SliceIter")))
    }

    /// `core::slice::IterMut`, the iterator `<[T]>::iter_mut` returns.
    pub fn slice_iter_mut(&self) -> Option<DefId> {
        *self
            .def_ids
            .slice_iter_mut
            .get_or_init(|| self.sibling_of(self.slice_iter()?, "IterMut"))
    }

    /// `alloc::vec::IntoIter`, the iterator `<Vec<T> as IntoIterator>::into_iter` returns.
    pub fn vec_into_iter(&self) -> Option<DefId> {
        *self
            .def_ids
            .vec_into_iter
            .get_or_init(|| self.sibling_of(self.vec()?, "IntoIter"))
    }

    fn annotated_def(&self, path: &[Symbol]) -> Option<DefId> {
        for item_id in self.tcx.hir_free_items() {
            let def_id = item_id.owner_id.to_def_id();
            if crate::analyze::annot::has_thrust_attr(self.tcx, def_id, path) {
                return Some(def_id);
            }

            let item = self.tcx.hir_item(item_id);
            if let rustc_hir::ItemKind::Trait(_, _, _, _, _, _, trait_item_refs) = item.kind {
                for trait_item_ref in trait_item_refs {
                    let def_id = trait_item_ref.owner_id.to_def_id();
                    if crate::analyze::annot::has_thrust_attr(self.tcx, def_id, path) {
                        return Some(def_id);
                    }
                }
            }
            if let rustc_hir::ItemKind::Impl(impl_) = item.kind {
                for impl_item_ref in impl_.items {
                    let def_id = impl_item_ref.owner_id.to_def_id();
                    if crate::analyze::annot::has_thrust_attr(self.tcx, def_id, path) {
                        return Some(def_id);
                    }
                }
            }
        }
        None
    }

    /// The formula of the `for` loop ghost the marker `def_id` makes, if it is one.
    pub fn for_loop_ghost_formula(&self, def_id: DefId) -> Option<DefId> {
        let formula = if Some(def_id) == self.for_loop_iter_old_marker() {
            self.for_loop_iter_old()
        } else if Some(def_id) == self.for_loop_produced_marker() {
            self.for_loop_produced()
        } else if Some(def_id) == self.for_loop_produced_push_marker() {
            self.for_loop_produced_push()
        } else {
            return None;
        };
        Some(formula.expect("a `for` loop ghost marker has its formula"))
    }

    /// The loop-invariant marker `def_id` is, if it is one.
    pub fn invariant_marker_kind(&self, def_id: DefId) -> Option<InvariantMarker> {
        if Some(def_id) == self.invariant_marker() {
            Some(InvariantMarker::Full)
        } else if Some(def_id) == self.partial_invariant_marker() {
            Some(InvariantMarker::Partial)
        } else if Some(def_id) == self.for_loop_history_marker() {
            Some(InvariantMarker::ForLoopHistory)
        } else {
            None
        }
    }
}
