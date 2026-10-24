//! Translation of subtyping relations into CHC constraints.

use rustc_index::IndexVec;

use crate::chc;
use crate::chc::debug;
use crate::pretty::PrettyDisplayExt;

use super::{
    ClauseBuilderExt as _, EnumDefProvider, FunctionParamIdx, FunctionType, PointerKind, RefKind,
    RefinedType, RefinedTypeVar, Refinement, Type,
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
///
/// A scope also gives the definitions of enums, from which the facts of their payloads are read
/// ([`RefinedType::formula_with`]); without them a value's facts leave its enum payloads out.
pub trait ClauseScope {
    fn build_clause(&self) -> chc::ClauseBuilder;

    fn enum_defs(&self) -> Option<&dyn EnumDefProvider>;
}

impl<T> ClauseScope for &T
where
    T: ClauseScope,
{
    fn build_clause(&self) -> chc::ClauseBuilder {
        T::build_clause(self)
    }

    fn enum_defs(&self) -> Option<&dyn EnumDefProvider> {
        T::enum_defs(self)
    }
}

impl ClauseScope for chc::ClauseBuilder {
    fn build_clause(&self) -> chc::ClauseBuilder {
        self.clone()
    }

    fn enum_defs(&self) -> Option<&dyn EnumDefProvider> {
        None
    }
}

/// A clause builder as a scope, with the definitions of enums.
pub struct ScopedBuilder<'a> {
    pub builder: chc::ClauseBuilder,
    pub enum_defs: Option<&'a dyn EnumDefProvider>,
}

impl ClauseScope for ScopedBuilder<'_> {
    fn build_clause(&self) -> chc::ClauseBuilder {
        self.builder.clone()
    }

    fn enum_defs(&self) -> Option<&dyn EnumDefProvider> {
        self.enum_defs
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
        (Type::Int(_) | Type::UInt(_), Type::Int(_) | Type::UInt(_))
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
            let mut builder = ScopedBuilder {
                builder: chc::ClauseBuilder::default(),
                enum_defs: scope.enum_defs(),
            };
            for (param_idx, param_rty) in got.params.iter_enumerated() {
                let param_sort = param_rty.ty.to_sort();
                if !param_sort.is_singleton() {
                    let chc_var = builder
                        .builder
                        .add_mapped_var(param_idx, param_sort.clone());
                    builder.builder.add_environment_origin(
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

    // A clause whose head is `true` is dropped by `push_clause`, so it is not built: building
    // one instantiates the whole environment.
    let head = head_of(&got.ty, &expected, position);
    if !head.is_top() {
        let cs = scope
            .build_clause()
            .with_value_var(&got.ty)
            .add_body(got.formula_with(scope.enum_defs()))
            .head(head);
        clauses.extend(cs);
    }

    if relation == Relation::Equal {
        let head = head_of(&expected.ty, &got, position);
        if !head.is_top() {
            let cs = scope
                .build_clause()
                .with_value_var(&expected.ty)
                .add_body(expected.formula_with(scope.enum_defs()))
                .head(head);
            clauses.extend(cs);
        }
    }

    clauses
}

/// The head of a clause relating a value of `got_ty` to `expected`: the refinement of `expected`,
/// and, at the top, the range of [`Type::UInt`] at each position where a value enters it.
///
/// A value of [`Type::UInt`] is assumed in its range wherever it is in the environment, so an
/// integer that becomes one, such as the result of a cast or of a checked operation, has to be
/// shown in range where it does. A nested position is checked through the value at the top,
/// whose refinement is what says something about it.
fn head_of<T, U>(got_ty: &Type<T>, expected: &RefinedType<U>, position: Position) -> Refinement<U>
where
    T: chc::Var,
    U: chc::Var,
{
    let mut head = expected.refinement.clone();
    if position == Position::Top {
        head.push_conj(int_range_facts(got_ty, &expected.ty));
    }
    head
}

/// The range of the integer type of `expected` at each position where a value of `got` enters
/// it: `v >= 0` where an integer of [`Type::Int`] becomes a [`Type::UInt`], and the bounds of
/// [`super::int_range`] where `got` is not a type within that range, through tuples and the
/// current value of pointers, and of each element of a sequence of such a type. The final value of a mutable reference is produced by its borrower,
/// which is checked where it writes it.
fn int_range_facts<T, U>(got: &Type<T>, expected: &Type<U>) -> Refinement<U>
where
    T: chc::Var,
    U: chc::Var,
{
    let value = || chc::Term::var(RefinedTypeVar::Value);
    let mut facts = Refinement::top();
    match (got, expected) {
        (Type::Int(_) | Type::UInt(_), Type::Int(_) | Type::UInt(_)) => {
            let bounds = super::int_range_bounds(expected, value()).expect("an integer type");
            // An unsigned value entering an unsigned type is already `>= 0`.
            let nonnegative = matches!((got, expected), (Type::UInt(_), Type::UInt(_)));
            let in_range = fits(got, expected);
            if let Some(atom) = bounds.lower.filter(|_| !in_range && !nonnegative) {
                facts.push_conj(atom.into());
            }
            if let Some(atom) = bounds.upper.filter(|_| !in_range) {
                facts.push_conj(atom.into());
            }
        }
        (Type::Seq(got), Type::Seq(expected)) if !fits(&got.ty, &expected.ty) => {
            if let Some(range) = super::seq_elem_range(&expected.ty, value()) {
                facts.push_conj(range.into());
            }
        }
        (Type::Tuple(got), Type::Tuple(expected)) if got.elems.len() == expected.elems.len() => {
            for (index, (got, expected)) in got.elems.iter().zip(&expected.elems).enumerate() {
                facts.push_conj(
                    int_range_facts(&got.ty, &expected.ty)
                        .subst_value_var(|| value().tuple_proj(index)),
                );
            }
        }
        (Type::Pointer(got), Type::Pointer(expected)) if got.kind == expected.kind => {
            facts.push_conj(
                int_range_facts(&got.elem.ty, &expected.elem.ty)
                    .subst_value_var(|| expected.kind.deref_term(value())),
            );
        }
        // An enum's payloads have facts under `THRUST_INT_RANGE` (`RefinedType::formula_with`);
        // a value entering the type at other arguments would have to be checked against them,
        // which is done only where a ghost term makes a value (`super::type_fact_checks`).
        (Type::Enum(got), Type::Enum(expected))
            if super::int_range_mode() != super::IntRange::Off
                && got.clone().strip_refinement() != expected.clone().strip_refinement() =>
        {
            unimplemented!(
                "a value of {} entering {} under THRUST_INT_RANGE",
                got.display(),
                expected.display()
            )
        }
        _ => {}
    }
    facts
}

#[must_use]
pub fn relate_sub_param_types(
    got: &IndexVec<FunctionParamIdx, RefinedType<FunctionParamIdx>>,
    expected: &IndexVec<FunctionParamIdx, RefinedType<FunctionParamIdx>>,
    enum_defs: Option<&dyn EnumDefProvider>,
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

    // A parameter's refinement is assumed of the parameters after it, as at a call site.
    for ((param_idx, got_ty), expected_ty) in got.iter_enumerated().zip(expected.iter()) {
        let scope = ScopedBuilder {
            builder: builder.clone(),
            enum_defs,
        };
        clauses.extend(scope.relate_sub_refined_type(expected_ty, got_ty));
        if expected_ty.refinement.is_top() {
            continue;
        }
        if expected_ty.ty.to_sort().is_singleton() {
            builder
                .with_value_var(&expected_ty.ty)
                .add_body(expected_ty.formula_with(enum_defs));
        } else {
            builder
                .with_mapped_value_var(param_idx)
                .add_body(expected_ty.formula_with(enum_defs));
        }
    }

    clauses
}

/// The clauses for `got`, the contract of a method of a trait impl, to refine `expected`, the
/// trait's contract of that method at the impl: under `expected`'s precondition, `got`'s holds and
/// `got`'s postcondition implies `expected`'s.
///
/// This is Creusot's refinement obligation (`translation/traits.rs`, `logic_refinement_term`).
/// Unlike the subtyping of two function types, the parameters are related at the same values and
/// the postconditions under `expected`'s precondition.
#[must_use]
pub fn relate_refining_function_type(
    got: &FunctionType,
    expected: &FunctionType,
    enum_defs: Option<&dyn EnumDefProvider>,
) -> Vec<chc::Clause> {
    assert_eq!(got.params.len(), expected.params.len());

    let mut builder = chc::ClauseBuilder::default();
    for (param_idx, param_rty) in expected.params.iter_enumerated() {
        let param_sort = param_rty.ty.to_sort();
        if !param_sort.is_singleton() {
            let chc_var = builder.add_mapped_var(param_idx, param_sort.clone());
            builder.add_environment_origin(
                debug::origin::Entry::parameter(param_idx, &param_sort)
                    .var_mapping(param_idx, chc_var),
            );
        }
    }
    for (param_idx, param_rty) in expected.params.iter_enumerated() {
        builder
            .with_mapped_value_var(param_idx)
            .add_body(param_rty.formula_with(enum_defs));
    }

    let mut clauses = Vec::new();
    for ((param_idx, got_rty), expected_rty) in got.params.iter_enumerated().zip(&expected.params) {
        let scope = ScopedBuilder {
            builder: builder.clone(),
            enum_defs,
        };
        clauses.extend(relate_type(
            &scope,
            &expected_rty.ty,
            &got_rty.ty,
            Relation::Sub,
        ));
        if !got_rty.refinement.is_top() {
            clauses.extend(
                builder
                    .clone()
                    .with_mapped_value_var(param_idx)
                    .head(got_rty.refinement.clone()),
            );
        }
    }
    let scope = ScopedBuilder {
        builder: builder.clone(),
        enum_defs,
    };
    clauses.extend(relate_type(
        &scope,
        &got.ret.ty,
        &expected.ret.ty,
        Relation::Sub,
    ));
    if !expected.ret.refinement.is_top() {
        clauses.extend(
            builder
                .clone()
                .with_value_var(&got.ret.ty)
                .add_body(got.ret.formula_with(enum_defs))
                .head(expected.ret.refinement.clone()),
        );
    }
    clauses
}

/// Whether every value of the integer type `got` is in the range of the integer type `expected`.
fn fits<T, U>(got: &Type<T>, expected: &Type<U>) -> bool {
    match (got, expected) {
        (Type::UInt(Some(got)), Type::UInt(Some(expected))) => got <= expected,
        (Type::UInt(Some(got)), Type::Int(Some(expected))) => got < expected,
        (Type::Int(Some(got)), Type::Int(Some(expected))) => got <= expected,
        _ => false,
    }
}
