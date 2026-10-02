# Inferring `hist_inv!` of a closure's by-value captures

An `FnMut` closure's `hist_inv!` relation is derived from its captures, and says nothing of a
capture taken by value, which the closure may replace. A `closure!` can state that part in a
`hist_inv` clause (`../closure_hist_inv_clause*.rs`); without one, Thrust infers it as an unknown
over the by-value captures at two states, reflexive and transitive by clauses and implied by each
call's postcondition. The tests here are the clause tests without the clause, and the steps
toward std's `filter`, whose `Filter::next` calls `find(&mut self.predicate)`. Each fail twin
(`../../fail/hist_inv_infer/`) makes a claim no closure contract implies.

| file | what it needs | state |
| --- | --- | --- |
| `counter.rs` | a counter owned by the closure, never decreasing | verifies |
| `owned_closure.rs` | a closure owning an `F: FnMut`, related through `F`'s `hist_inv!` (the unknown depends on that universal predicate) | verifies |
| `mut_ref_closure.rs` | `&mut F` passed as an `FnMut` by value, its states read back as `f`'s | ignored, with its fail twin: the frontend panics (`src/analyze/annot_fn.rs`, precondition of a non-closure parameter) |
| `find.rs` | std's `find` through `try_fold`, `check` without its clause | ignored: the solver raises on `find`'s postcondition (as `../creusot/generic/std/find.rs`) |
