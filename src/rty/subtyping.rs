//! Translation of subtyping relations into CHC constraints.

use rustc_index::IndexVec;

use crate::chc;
use crate::chc::debug;
use crate::pretty::PrettyDisplayExt;

use super::{
    ClauseBuilderExt as _, FunctionParamIdx, PointerKind, RefKind, RefinedType, RefinedTypeVar,
    Refinement, Type,
};

#[cfg(test)]
mod tests;

/// A scope for building clauses.
///
/// The construction of CHC clauses requires knowledge of the current
/// environment to determine variable sorts and include necessary premises.
/// This trait abstracts the preparation of a [`chc::ClauseBuilder`] to allow an
/// environment defined outside of this module (in Thrust, [`crate::refine::Env`])
/// to build a [`chc::ClauseBuilder`] equipped with in-scope variables and assumptions.
pub trait ClauseScope {
    fn build_clause(&self) -> chc::ClauseBuilder;
}

impl<T> ClauseScope for &T
where
    T: ClauseScope,
{
    fn build_clause(&self) -> chc::ClauseBuilder {
        T::build_clause(self)
    }
}

impl ClauseScope for chc::ClauseBuilder {
    fn build_clause(&self) -> chc::ClauseBuilder {
        self.clone()
    }
}

/// Produces CHC constraints for subtyping relations.
pub trait Subtyping {
    #[must_use]
    fn relate_sub_refined_type<T: chc::Var, U: chc::Var>(
        &self,
        got: &RefinedType<T>,
        expected: &RefinedType<U>,
    ) -> Vec<chc::Clause>;
}

impl<C> Subtyping for C
where
    C: ClauseScope,
{
    fn relate_sub_refined_type<T, U>(
        &self,
        got: &RefinedType<T>,
        expected: &RefinedType<U>,
    ) -> Vec<chc::Clause>
    where
        T: chc::Var,
        U: chc::Var,
    {
        relate_refined_type(self, got, expected, Relation::Sub, Position::Top)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Relation {
    Sub,
    Equal,
}

/// Whether the value variable of a relation is the value related, or a position in a type related
/// by an enclosing relation (an element, a pointee, a parameter or the result of a function type),
/// whose value variable is bound afresh and stands for any value of that position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Position {
    Top,
    Nested,
}

#[must_use]
fn relate_type<C, T, U>(
    scope: &C,
    got: &Type<T>,
    expected: &Type<U>,
    relation: Relation,
) -> Vec<chc::Clause>
where
    C: ClauseScope,
    T: chc::Var,
    U: chc::Var,
{
    tracing::debug!(got = %got.display(), expected = %expected.display(), ?relation, "relate_type");

    let mut clauses = Vec::new();
    match (got, expected) {
        (Type::Int | Type::UInt, Type::Int | Type::UInt)
        | (Type::Bool, Type::Bool)
        | (Type::String, Type::String)
        | (Type::Never, Type::Never) => {}
        (Type::BitVec(got), Type::BitVec(expected)) if got == expected => {}
        (Type::Enum(got), Type::Enum(expected)) if got.symbol() == expected.symbol() => {
            for (got_ty, expected_ty) in got.args.iter().zip(expected.args.iter()) {
                let cs =
                    relate_refined_type(scope, got_ty, expected_ty, relation, Position::Nested);
                clauses.extend(cs);
            }
        }
        (Type::Tuple(got), Type::Tuple(expected)) if got.elems.len() == expected.elems.len() => {
            for (got_ty, expected_ty) in got.elems.iter().zip(expected.elems.iter()) {
                let cs =
                    relate_refined_type(scope, got_ty, expected_ty, relation, Position::Nested);
                clauses.extend(cs);
            }
        }
        (Type::Pointer(got), Type::Pointer(expected)) if got.kind == expected.kind => {
            let elem_relation = match got.kind {
                PointerKind::Ref(RefKind::Immut) => relation,
                PointerKind::Own | PointerKind::Ref(RefKind::Mut) => Relation::Equal,
            };
            let cs = relate_refined_type(
                scope,
                &got.elem,
                &expected.elem,
                elem_relation,
                Position::Nested,
            );
            clauses.extend(cs);
        }
        (Type::Function(got), Type::Function(expected))
            if got.params.len() == expected.params.len() =>
        {
            let mut builder = chc::ClauseBuilder::default();
            for (param_idx, param_rty) in got.params.iter_enumerated() {
                let param_sort = param_rty.ty.to_sort();
                if !param_sort.is_singleton() {
                    let chc_var = builder.add_mapped_var(param_idx, param_sort.clone());
                    builder.add_environment_origin(
                        debug::origin::Entry::parameter(param_idx, &param_sort)
                            .var_mapping(param_idx, chc_var),
                    );
                }
            }
            for (got_ty, expected_ty) in got.params.iter().zip(expected.params.iter()) {
                let cs =
                    relate_refined_type(&builder, expected_ty, got_ty, relation, Position::Nested);
                clauses.extend(cs);
            }
            let cs = relate_refined_type(
                &builder,
                &got.ret,
                &expected.ret,
                relation,
                Position::Nested,
            );
            clauses.extend(cs);
        }
        (Type::Seq(got), Type::Seq(expected)) => {
            clauses.extend(relate_refined_type(
                scope,
                got,
                expected,
                relation,
                Position::Nested,
            ));
        }
        (Type::Array(got), Type::Array(expected)) => {
            let cs1 = relate_refined_type(
                scope,
                &got.index,
                &expected.index,
                relation,
                Position::Nested,
            );
            clauses.extend(cs1);
            let cs2 =
                relate_refined_type(scope, &got.elem, &expected.elem, relation, Position::Nested);
            clauses.extend(cs2);
        }
        (Type::Param(got), Type::Param(expected))
            if got.forall_sort_idx == expected.forall_sort_idx => {}
        (Type::Alias(got), Type::Alias(expected))
            if got.forall_sort_index() == expected.forall_sort_index() => {}
        _ => panic!(
            "inconsistent types: got={}, expected={}",
            got.display(),
            expected.display()
        ),
    }
    clauses
}

#[must_use]
fn relate_refined_type<C, T, U>(
    scope: &C,
    got: &RefinedType<T>,
    expected: &RefinedType<U>,
    relation: Relation,
    position: Position,
) -> Vec<chc::Clause>
where
    C: ClauseScope,
    T: chc::Var,
    U: chc::Var,
{
    tracing::debug!(got = %got.display(), expected = %expected.display(), ?relation, "relate_refined_type");

    let got = got.clone().normalize_tuple_refinements();
    let expected = expected.clone().normalize_tuple_refinements();
    let mut clauses = relate_type(scope, &got.ty, &expected.ty, relation);

    let cs = scope
        .build_clause()
        .with_value_var(&got.ty)
        .add_body(got.formula())
        .head(head_of(&got.ty, &expected, position));
    clauses.extend(cs);

    if relation == Relation::Equal {
        let cs = scope
            .build_clause()
            .with_value_var(&expected.ty)
            .add_body(expected.formula())
            .head(head_of(&expected.ty, &got, position));
        clauses.extend(cs);
    }

    clauses
}

/// The head of a clause relating a value of `got_ty` to `expected`: the refinement of `expected`,
/// and, at the top, `v >= 0` at each position where a value of [`Type::Int`] is related to one of
/// [`Type::UInt`].
///
/// A value of [`Type::UInt`] is assumed non-negative wherever it is in the environment, so an
/// integer that becomes one, such as the result of a cast or of a checked operation, has to be
/// shown non-negative where it does. A nested position is checked through the value at the top,
/// whose refinement is what says something about it.
fn head_of<T, U>(got_ty: &Type<T>, expected: &RefinedType<U>, position: Position) -> Refinement<U>
where
    U: chc::Var,
{
    let mut head = expected.refinement.clone();
    if position == Position::Top {
        head.push_conj(uint_facts_of_int(got_ty, &expected.ty));
    }
    head
}

/// `v >= 0` at each position where `got` has [`Type::Int`] and `expected` has [`Type::UInt`],
/// through tuples and the current value of pointers. The final value of a mutable reference is
/// produced by its borrower, which is checked where it writes it.
fn uint_facts_of_int<T, U>(got: &Type<T>, expected: &Type<U>) -> Refinement<U>
where
    U: chc::Var,
{
    let value = || chc::Term::var(RefinedTypeVar::Value);
    let mut facts = Refinement::top();
    match (got, expected) {
        (Type::Int, Type::UInt) => {
            facts.push_conj(
                chc::Atom::new(
                    chc::KnownPred::GREATER_THAN_OR_EQUAL.into(),
                    vec![value(), chc::Term::int(0)],
                )
                .into(),
            );
        }
        (Type::Tuple(got), Type::Tuple(expected)) if got.elems.len() == expected.elems.len() => {
            for (index, (got, expected)) in got.elems.iter().zip(&expected.elems).enumerate() {
                facts.push_conj(
                    uint_facts_of_int(&got.ty, &expected.ty)
                        .subst_value_var(|| value().tuple_proj(index)),
                );
            }
        }
        (Type::Pointer(got), Type::Pointer(expected)) if got.kind == expected.kind => {
            facts.push_conj(
                uint_facts_of_int(&got.elem.ty, &expected.elem.ty)
                    .subst_value_var(|| expected.kind.deref_term(value())),
            );
        }
        _ => {}
    }
    facts
}

#[must_use]
pub fn relate_sub_param_types(
    got: &IndexVec<FunctionParamIdx, RefinedType<FunctionParamIdx>>,
    expected: &IndexVec<FunctionParamIdx, RefinedType<FunctionParamIdx>>,
) -> Vec<chc::Clause> {
    assert_eq!(got.len(), expected.len());

    let mut clauses = Vec::new();
    let mut builder = chc::ClauseBuilder::default();

    for (param_idx, param_rty) in got.iter_enumerated() {
        let param_sort = param_rty.ty.to_sort();
        if !param_sort.is_singleton() {
            let chc_var = builder.add_mapped_var(param_idx, param_sort.clone());
            builder.add_environment_origin(
                debug::origin::Entry::parameter(param_idx, &param_sort)
                    .var_mapping(param_idx, chc_var),
            );
        }
    }

    for (got_ty, expected_ty) in got.iter().zip(expected.iter()) {
        let cs = builder.relate_sub_refined_type(expected_ty, got_ty);
        clauses.extend(cs);
    }

    clauses
}
