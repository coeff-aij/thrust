# Derived trait predicates

A `#[thrust_macros::predicate(derived)]` of a trait that an impl leaves out is declared as an
unknown. Its rules are the checks of the `ensures` of the impl's functions and laws; any other
check that concludes it, a rule that is not definite in it, an unanalyzed function of the impl,
and an unproven assumption with it negated or in a premise (a function's own precondition, a
trusted function's postcondition) are rejected (`src/analyze/derived_pred.rs`). Each fail twin
and each rejected file is in `../../fail/derived_pred/`.

| file | what it shows | state |
| --- | --- | --- |
| `map_call.rs` | `creusot/weaker/map_call` with `Range::produces` left out; `main` assumes it through `Map::invariant` | verifies; the fail twin is refuted |
| `take.rs` | `creusot/take` with `Range::produces` left out; `main` reads the first item of `Take<Range>` through it | verifies; the fail twins `take.rs` (a defect in `Take::produces`) and `take_value.rs` (an item `Range` never yields first) are refuted |
| `try_fold.rs` | `creusot/try_fold` with `Range::produces` left out; the loop reads each item's lower bound from `next`'s `produces` | verifies; the fail twin is refuted |
| `checked_assumption.rs` | an analyzed function's `ensures` negates `produces`, and `main` assumes it | verifies: the assumption is proven in the system |
| `law_only_impl.rs` | an impl with no function; the rule is the inherited law, analyzed under the impl | verifies |
| `../../fail/derived_pred/client_requires.rs` | a precondition at a call outside the impl concludes it | rejected |
| `../../fail/derived_pred/inherent_impl.rs` | an inherent impl of `Range` concludes it | rejected: only the trait's impl for the type is a rule site |
| `../../fail/derived_pred/other_trait_args.rs` | the impl of `Tr<bool>` concludes the predicate derived at `Tr<isize>` for the same type | rejected |
| `../../fail/derived_pred/call_in_rule_site.rs` | a call inside `next` whose precondition concludes it | rejected: not a check of `next`'s `ensures` |
| `../../fail/derived_pred/loop_invariant.rs` | a loop invariant concludes it at the back edge | rejected |
| `../../fail/derived_pred/disjunctive_rule.rs` | `next`'s `ensures` concludes it of one of two states | rejected: not definite |
| `../../fail/derived_pred/trusted_next.rs` | `next` is trusted | rejected: no rule from its body |
| `../../fail/derived_pred/trusted_assumption.rs` | a trusted function's `ensures` has it in a premise | rejected |
| `../../fail/derived_pred/requires_premise.rs`, `requires_negated.rs` | a function's own `requires` has it in a premise, negated | rejected |
| `../../fail/derived_pred/generic_impl.rs` | a generic impl leaves it out | rejected |
| `../../fail/derived_pred/not_in_trait.rs`, `impl_item.rs` | the attribute on a free function, on an impl's item | rejected |
