//! The refinement type for a basic block.

use std::collections::HashMap;

use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;
use rustc_middle::mir::{BasicBlock, Local};
use rustc_middle::ty as mir_ty;

use crate::chc;
use crate::rty;

#[derive(Debug, Clone)]
pub enum BasicBlockTypeParamKind {
    Local(Local, mir_ty::Mutability),
    OuterFnParam(rty::FunctionParamIdx),
    Synthetic,
    /// The value `Local` had when the loop headed by `BasicBlock` was entered.
    EntrySnapshot(BasicBlock, Local),
    Captured,
}

impl BasicBlockTypeParamKind {
    pub fn local(&self) -> Option<Local> {
        match self {
            BasicBlockTypeParamKind::Local(local, _) => Some(*local),
            _ => None,
        }
    }

    pub fn outer_fn_param_idx(&self) -> Option<rty::FunctionParamIdx> {
        match self {
            BasicBlockTypeParamKind::OuterFnParam(idx) => Some(*idx),
            _ => None,
        }
    }
}

/// A special case of [`rty::FunctionType`] whose parameters are associated with [`Local`]s.
///
/// Thrust handles basic blocks as functions, but it needs to associate function
/// parameters with MIR [`Local`]s during its analysis. [`BasicBlockType`] includes this mapping
/// from function parameters to [`Local`]s, along with the underlying function type.
#[derive(Debug, Clone)]
pub struct BasicBlockType {
    // TODO: make this completely private by exposing appropriate ctor
    pub(super) ty: rty::FunctionType,
    pub(super) locals: IndexVec<rty::FunctionParamIdx, (Local, mir_ty::Mutability)>,
    // XXX: needs this to disambiguate synthetic unit param from outer fn unit param
    pub(super) outer_fn_param_count: usize,
    pub(super) captured_param_count: usize,
    /// The entry snapshots of the loops the block is in, which come before the captured values.
    pub(super) entry_snapshots: Vec<(BasicBlock, Local)>,
    /// What holds of the entry snapshots, assumed on entering the block and not required of an
    /// edge into it (see [`crate::analyze::loop_frame`]).
    pub(super) assumed_entry_state: rty::Refinement<rty::FunctionParamIdx>,
    /// What the existentials of the precondition hold, for the report, when it is inherited
    /// from the block before (see [`BasicBlockType::describe_precondition`]).
    pub(super) precondition_names: crate::refine::ExistentialNames,
}

impl<'a, D> Pretty<'a, D, termcolor::ColorSpec> for &BasicBlockType
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let separator = allocator.text(",").append(allocator.line());
        let params = self.ty.params.iter_enumerated().map(|(idx, ty)| {
            if let Some((local, mutbl)) = self.locals.get(idx) {
                allocator
                    .text(format!("{}{:?}:", mutbl.prefix_str(), local))
                    .append(allocator.space())
                    .append(ty.pretty(allocator))
            } else {
                ty.pretty(allocator)
            }
        });
        allocator
            .intersperse(params, separator)
            .parens()
            .append(allocator.space())
            .append(allocator.text("→"))
            .append(allocator.line())
            .append(self.ty.ret.pretty(allocator))
            .group()
    }
}

impl AsRef<rty::FunctionType> for BasicBlockType {
    fn as_ref(&self) -> &rty::FunctionType {
        &self.ty
    }
}

impl BasicBlockType {
    pub fn param_kind(&self, idx: rty::FunctionParamIdx) -> BasicBlockTypeParamKind {
        let snapshots_start =
            self.ty.params.len() - self.captured_param_count - self.entry_snapshots.len();
        if idx.index() >= self.ty.params.len() - self.captured_param_count {
            BasicBlockTypeParamKind::Captured
        } else if idx.index() >= snapshots_start {
            let (head, local) = self.entry_snapshots[idx.index() - snapshots_start];
            BasicBlockTypeParamKind::EntrySnapshot(head, local)
        } else if let Some((local, mutbl)) = self.locals.get(idx) {
            BasicBlockTypeParamKind::Local(*local, *mutbl)
        } else if idx.index() >= self.locals.len() && self.outer_fn_param_count > 0 {
            BasicBlockTypeParamKind::OuterFnParam(rty::FunctionParamIdx::from(
                idx.index() - self.locals.len(),
            ))
        } else {
            BasicBlockTypeParamKind::Synthetic
        }
    }

    pub fn local_of_param(&self, idx: rty::FunctionParamIdx) -> Option<Local> {
        self.param_kind(idx).local()
    }

    pub fn mutbl_of_param(&self, idx: rty::FunctionParamIdx) -> Option<mir_ty::Mutability> {
        if let BasicBlockTypeParamKind::Local(_, mutbl) = self.param_kind(idx) {
            Some(mutbl)
        } else {
            None
        }
    }

    pub fn local_params(&self) -> impl DoubleEndedIterator<Item = rty::FunctionParamIdx> + '_ {
        self.locals.indices()
    }

    pub fn locals(&self) -> impl Iterator<Item = Local> + '_ {
        self.ty
            .params
            .iter_enumerated()
            .filter_map(|(idx, _)| self.local_of_param(idx))
    }

    pub fn param_of_local(&self, local: Local) -> Option<rty::FunctionParamIdx> {
        self.locals
            .iter_enumerated()
            .find_map(|(idx, (l, _))| if *l == local { Some(idx) } else { None })
    }

    pub fn param_of_entry_snapshot(
        &self,
        head: BasicBlock,
        local: Local,
    ) -> Option<rty::FunctionParamIdx> {
        let position = self
            .entry_snapshots
            .iter()
            .position(|&s| s == (head, local))?;
        let first = self.ty.params.len() - self.captured_param_count - self.entry_snapshots.len();
        Some(rty::FunctionParamIdx::from(first + position))
    }

    pub fn param_of_outer_fn_param(
        &self,
        idx: rty::FunctionParamIdx,
    ) -> Option<rty::FunctionParamIdx> {
        if idx.index() < self.outer_fn_param_count {
            Some(rty::FunctionParamIdx::from(self.locals.len() + idx.index()))
        } else {
            None
        }
    }

    pub fn to_function_ty(&self) -> rty::FunctionType {
        self.ty.clone()
    }

    /// Adds a parameter for the value `local` had when the loop headed by `head` was entered.
    /// It must come before any captured parameter.
    pub fn push_entry_snapshot_param(
        &mut self,
        head: BasicBlock,
        local: Local,
        ty: rty::Type<rty::Closed>,
    ) -> rty::FunctionParamIdx {
        assert_eq!(self.captured_param_count, 0);
        self.entry_snapshots.push((head, local));
        self.ty
            .params
            .push(rty::RefinedType::unrefined(ty.vacuous()))
    }

    /// Requires the parameter `idx` to satisfy `refinement`, over the other parameters.
    pub fn require_of_param(
        &mut self,
        idx: rty::FunctionParamIdx,
        refinement: rty::Refinement<rty::FunctionParamIdx>,
    ) {
        self.ty.params[idx].refinement.push_conj(refinement);
    }

    /// Assumes `precondition`, the precondition of the landing `landing` of the loop headed by
    /// `head`, over the entry values of this block, with the values it has none of left unknown.
    /// The entry value of a variable is its entry snapshot, or the parameter that holds it when
    /// the block has no snapshot of it (the loop does not write it); of a `&mut` the loop writes
    /// through, only its final value is the snapshot, and its current value is left unknown.
    pub fn assume_entry_state(
        &mut self,
        head: BasicBlock,
        landing: &BasicBlockType,
        is_kept: impl Fn(Local) -> bool,
    ) {
        let last = landing.precondition_param();
        let precondition = landing.ty.params[last].refinement.clone();
        let mut existentials = precondition.existentials.clone();
        let mut value_of = Vec::new();
        let mut final_values = Vec::new();
        for (idx, param) in landing.ty.params.iter_enumerated() {
            let sort = param.ty.to_sort();
            let known = match landing.param_kind(idx) {
                BasicBlockTypeParamKind::Local(local, _) => self
                    .param_of_entry_snapshot(head, local)
                    .or_else(|| self.param_of_local(local).filter(|_| is_kept(local))),
                BasicBlockTypeParamKind::OuterFnParam(outer) => self.param_of_outer_fn_param(outer),
                BasicBlockTypeParamKind::Synthetic
                | BasicBlockTypeParamKind::EntrySnapshot(..)
                | BasicBlockTypeParamKind::Captured => None,
            };
            let var = match known {
                Some(own) if self.ty.params[own].ty.to_sort() == sort => {
                    rty::RefinedTypeVar::Free(own)
                }
                Some(own) => {
                    let value = existentials.push(sort);
                    final_values.push((value, own, param.ty.clone()));
                    rty::RefinedTypeVar::Existential(value)
                }
                None => rty::RefinedTypeVar::Existential(existentials.push(sort)),
            };
            value_of.push(var);
        }
        let mut body = precondition.body.map_var(|v| match v {
            rty::RefinedTypeVar::Value => value_of[last.index()],
            rty::RefinedTypeVar::Free(idx) => value_of[idx.index()],
            rty::RefinedTypeVar::Existential(ev) => rty::RefinedTypeVar::Existential(ev),
        });
        for (value, final_value, ty) in final_values {
            let value = chc::Term::var(rty::RefinedTypeVar::Existential(value));
            body.push_conj(
                final_value_term(&ty, value)
                    .equal_to(chc::Term::var(rty::RefinedTypeVar::Free(final_value))),
            );
        }
        self.assumed_entry_state
            .push_conj(rty::Refinement::new(existentials, body));
    }

    pub fn assumed_entry_state(&self) -> &rty::Refinement<rty::FunctionParamIdx> {
        &self.assumed_entry_state
    }

    pub fn push_captured_param(&mut self, ty: rty::Type<rty::Closed>) -> rty::FunctionParamIdx {
        self.captured_param_count += 1;
        self.ty
            .params
            .push(rty::RefinedType::unrefined(ty.vacuous()))
    }

    pub fn set_param_type(
        &mut self,
        idx: rty::FunctionParamIdx,
        ty: rty::Type<rty::FunctionParamIdx>,
    ) {
        self.ty.params[idx].ty = ty;
    }

    /// The parameter that carries the precondition: the last one that is not an entry snapshot,
    /// which are put after it. For a block that inherits the state of another, it is the last
    /// parameter captured from that block.
    pub fn precondition_param(&self) -> rty::FunctionParamIdx {
        self.ty
            .params
            .indices()
            .rev()
            .find(|&idx| {
                !matches!(
                    self.param_kind(idx),
                    BasicBlockTypeParamKind::EntrySnapshot(..)
                )
            })
            .expect("a block has a parameter for its precondition")
    }

    pub fn set_precondition(&mut self, refinement: rty::Refinement<rty::FunctionParamIdx>) {
        let precondition_idx = self.precondition_param();
        self.ty.params[precondition_idx].refinement = refinement.map_var(|v| {
            if v == rty::RefinedTypeVar::Free(precondition_idx) {
                rty::RefinedTypeVar::Value
            } else {
                v
            }
        });
    }

    /// Keeps what the existentials of the precondition hold: the variables of the block before,
    /// which an inherited precondition quantifies.
    pub fn describe_precondition(&mut self, names: crate::refine::ExistentialNames) {
        self.precondition_names = names;
    }

    pub fn precondition_names(&self) -> &crate::refine::ExistentialNames {
        &self.precondition_names
    }

    /// Adds `refinement` to the block's precondition, keeping what is there. On a block
    /// built for inference that is the template's predicate variable, so a written
    /// invariant then seeds inference instead of replacing it.
    pub fn conjoin_precondition(&mut self, refinement: rty::Refinement<rty::FunctionParamIdx>) {
        let precondition_idx = self.precondition_param();
        let mapped = refinement.map_var(|v| {
            if v == rty::RefinedTypeVar::Free(precondition_idx) {
                rty::RefinedTypeVar::Value
            } else {
                v
            }
        });
        self.ty.params[precondition_idx]
            .refinement
            .push_conj(mapped);
    }

    /// Inner function type of BasicBlockType contains extra parameters that carry original
    /// function parameter values. `truncate_outer_fn_params` removes these extra parameters
    /// to subtype output of [`BasicBlockType::to_function_ty`] against the function type.
    ///
    /// before: (_1: int, _2: int, int, { int |  p4 ν $0 $1 $2 }) → { int | p5 ν $0 $1 $2 $3 }
    /// after:  (_1: int, _2: { int | p4 v $0 $1 $0 }) → { int | p5 ν $0 $1 _1 _2 }
    ///
    /// FIXME: this should be (&self) -> FunctionType
    pub fn truncate_outer_fn_params(&mut self) {
        let last_param_idx = self.ty.params.last_index().unwrap();
        let last_param_ty = self.ty.params.raw.last().unwrap();

        let mut mapping = HashMap::new();
        for (idx, param_ty) in self.ty.params.iter_enumerated() {
            let mapped_idx = if let Some(outer_idx) = self.param_kind(idx).outer_fn_param_idx() {
                let corresponding_local = crate::analyze::local_of_function_param(outer_idx);
                self.param_of_local(corresponding_local).unwrap()
            } else {
                idx
            };
            mapping.insert(idx, mapped_idx);

            // to be sure: only the last parameter carries the predicate variable of the
            // precondition; the others carry at most what their model says about them.
            if idx != last_param_idx {
                assert!(!param_ty.refinement.has_pred_var());
            }
        }

        let last_param_refinement = last_param_ty.refinement.clone().map_var(|v| {
            let idx = match v {
                rty::RefinedTypeVar::Free(idx) => idx,
                rty::RefinedTypeVar::Value => last_param_idx,
                v => return v,
            };
            let mapped_idx = mapping[&idx];
            if Some(mapped_idx) == self.locals.last_index() {
                rty::RefinedTypeVar::Value
            } else {
                rty::RefinedTypeVar::Free(mapped_idx)
            }
        });

        if !self.locals.is_empty() {
            self.ty.params.truncate(self.locals.len());
        }

        self.ty.params.raw.last_mut().unwrap().refinement = last_param_refinement;
        self.ty.ret.refinement = self
            .ty
            .ret
            .refinement
            .clone()
            .map_free_var(|idx| mapping[&idx]);
    }
}

/// The type of the final value of a `&mut` of type `ty`, which is the whole of the local that
/// holds it when the local is boxed (a mutable local is).
pub fn final_value_type<T: Clone>(ty: &rty::Type<T>) -> rty::Type<T> {
    match ty.as_pointer() {
        Some(pointer) if pointer.is_own() => final_value_type(&pointer.elem.ty),
        Some(pointer) if pointer.is_mut() => pointer.elem.ty.clone(),
        _ => unreachable!("only a `&mut` keeps its final value alone"),
    }
}

/// The final value of the `&mut`, of type `ty`, that `term` holds.
pub fn final_value_term<T, V>(ty: &rty::Type<T>, term: chc::Term<V>) -> chc::Term<V> {
    match ty.as_pointer() {
        Some(pointer) if pointer.is_own() => final_value_term(&pointer.elem.ty, term.box_current()),
        Some(pointer) if pointer.is_mut() => term.mut_final(),
        _ => unreachable!("only a `&mut` keeps its final value alone"),
    }
}
