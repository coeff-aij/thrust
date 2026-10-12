# Derived trait predicates

A `#[thrust_macros::predicate(derived)]` of a trait that an impl leaves out is declared as an
unknown, defined by what the impl's own functions conclude of it; any other clause that concludes
it is rejected. Each fail twin is in `../../fail/derived_pred/`.

| file | what it shows | state |
| --- | --- | --- |
| `map_call.rs` | `creusot/weaker/map_call` with `Range::produces` left out; `main` assumes it through `Map::invariant` | verifies; the fail twin is refuted |
| `../../fail/derived_pred/client_requires.rs` | a precondition outside the impl concludes `Range::produces` | rejected |
