# Derived trait predicates

A `#[thrust_macros::predicate(derived)]` of a trait that an impl leaves out is declared as an
unknown, defined by what the impl's own functions conclude of it; any other clause that concludes
it is rejected. Each fail twin is in `../../fail/derived_pred/`.

| file | what it shows | state |
| --- | --- | --- |
| `map_call.rs` | `creusot/weaker/map_call` with `Range::produces` left out; `main` assumes it through `Map::invariant` | verifies; the fail twin is refuted |
| `take.rs` | `creusot/take` with `Range::produces` left out; `main` reads the first item of `Take<Range>` through it | verifies; the fail twins `take.rs` (a defect in `Take::produces`) and `take_value.rs` (an item `Range` never yields first) are refuted |
| `try_fold.rs` | `creusot/try_fold` with `Range::produces` left out; the loop reads each item's lower bound from `next`'s `produces` | verifies; the fail twin is refuted |
| `../../fail/derived_pred/client_requires.rs` | a precondition outside the impl concludes `Range::produces` | rejected |
| `../../fail/derived_pred/inherent_impl.rs` | an inherent impl of `Range` concludes `Range::produces` | rejected: only the trait's impl for the type is a rule site |
