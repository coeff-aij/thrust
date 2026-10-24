# Derived trait predicates

A `#[thrust_macros::predicate(derived)]` of a trait that an impl leaves out is an unknown of the
query, inferred like a loop invariant: every clause that mentions it is checked as with a written
body, and a solution gives the program's safety whatever relation it picks. It is declared with
no dependency on forall predicates, and a contract Thrust assumes without checking it against a
body (trusted, ignored, unselected, an extern specification, an inherited law not checked for its
impl) may not mention it or a predicate depending on it (`src/analyze/derived_pred.rs`). An
analyzed function whose precondition mentions it, entered from unanalyzed code, must accept every
argument there (D59). Fail twins and rejected files are in `../../fail/derived_pred/`.

| file | what it shows | state |
| --- | --- | --- |
| `map_call.rs` | `creusot/weaker/map_call` with `Range::produces` left out; `main` assumes it through `Map::invariant` | verifies; the fail twin is refuted |
| `take.rs` | `creusot/take` with `Range::produces` left out; `main` reads the first item of `Take<Range>` through it | verifies; the fail twins `take.rs` (a defect in `Take::produces`) and `take_value.rs` (an item `Range` never yields first) are refuted |
| `try_fold.rs` | `creusot/try_fold` with `Range::produces` left out | verifies; the fail twin is refuted |
| `checked_assumption.rs` | an analyzed function's `ensures` negates `produces`, and `main` assumes it | verifies |
| `law_only_impl.rs` | an impl with no function; the rule is the inherited law | verifies |
| `client_requires.rs`, `call_in_rule_site.rs`, `default_in_rule_site.rs`, `inherent_impl.rs`, `loop_invariant.rs`, `other_trait_args.rs` | a check outside the impl's `ensures` concludes the predicate of an item `next` never yields (a call's precondition, a call inside `next`, a default method, an inherent impl, a loop invariant, another trait instance) | verify: the inferred relation includes the item, and the program does not depend on what the relation is |
| `disjunctive_rule.rs` | `next`'s `ensures` concludes it of one of two states | verifies, likewise |
| `../../fail/derived_pred/trusted_next.rs`, `trusted_assumption.rs`, `trusted_generic.rs`, `trusted_default.rs`, `refine.rs`, `method_post.rs` | a trusted function's contract mentions it (`next`, a function, generic or a default method, an impl method weaker than the trait's, a method without a trait specification) | rejected |
| `../../fail/derived_pred/extern_spec.rs` | an extern specification of a foreign function mentions it | rejected |
| `../../fail/derived_pred/unselected_law.rs` | the inherited law outside `THRUST_VERIFY_ONLY` | rejected |
| `../../fail/derived_pred/via_trusted.rs`, `via_impl.rs`, `via_indirect.rs`, `via_closure.rs` | a trusted contract behind a verified generic function, through a trait method, a written trait predicate defined through it, a closure's contract | rejected |
| `../../fail/derived_pred/law_other.rs` | a law of another trait states that `Small` yields nothing | refuted: the predicate depends on no forall predicate |
| `../../fail/derived_pred/requires_premise.rs`, `requires_negated.rs` | a function whose precondition has it in a premise, negated, entered from a trusted function | refuted: the precondition must accept every argument there (D59) |
| `../../fail/derived_pred/generic_impl.rs` | a generic impl leaves it out | rejected |
| `../../fail/derived_pred/not_in_trait.rs`, `impl_item.rs` | the attribute on a free function, on an impl's item | rejected |
