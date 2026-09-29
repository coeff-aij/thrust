# Creusot benchmark drafts

What does not verify yet, and non-refuting fail twins, for the benchmark cases tracked under
`tests/ui/{pass,fail}/creusot/`. Full verdict tables and history are in `drafts/creusot-form/NOTES.md`
and `drafts/creusot-examples/NOTES.md` as of commit 382af70, before this directory replaced them.

## map_ext (fail twins)

Creusot's `MapInv` (the ninth adapter, `iterators/map_ext.rs`) moved to the tracked suite:
`tests/ui/pass/creusot/map_ext.rs` and its fail twin `tests/ui/fail/creusot/map_ext.rs` (`next`
does not extend `produced`). The other fail twins stay here:

- `fail/map_ext_pre.rs`: the closure requires `x == 1` (drops the history) — refutes.
- `fail/map_ext_value.rs`: the call site claims `Some(21)` — not re-measured since the two new
  lemmas were added.

## fuse_produces_result.rs (+ fail/)

`tests/ui/pass/creusot/fuse_produces.rs` with Creusot's state `Result<I, Ghost<I>>`: `Err` holds a
ghost of the exhausted inner iterator, taken after the inner `next` returns `None`, and `produces`
reads it through Creusot's `inner`. On fptprove 9e87f6a90 the pass side gives no answer at 300 s
and the fail twin refutes in 127 s. The laws (`produces_refl`, `produces_trans`, `is_fused`) check
alone in under 2 s; `next` alone is what stalls (no answer at 300 s), where with the `Option<I>`
state it answers in 5 s. Writing the predicates with `forall` instead of `exists`, or dropping
the `Err` payload's invariant, does not change that.

The ghost term names only live variables, so `next` keeps `iter` live past the ghost with an
unused shared borrow (`_keep`), as Creusot's `ghost! { *iter }` reads `iter`.

## counter_creusot.rs (+ fail/)

Creusot's `examples/counter` with its own property (`x == v`, `cnt == x.len()`) over a `Range`,
through `map_ext.rs`'s `MapInv` with an `FnMut` closure: `produces` carries the chain `fs` of
closure states and, as creusot-std's `std/iter/map_inv.rs`, relates them by `unnest!` (Creusot's
`hist_inv`); the closure's ensures adds `unnest(*self, ^self)` of Creusot's `postcondition_mut`
(the borrow of `cnt` keeps its prophecy). Stage S2: with the adapter's and `from_iter`'s bodies
trusted both conjuncts are decided and the fail twin (`cnt == x.len() + 1`) refutes; checked,
`from_iter`'s instance and the generic `produces_trans_witness` stall on the witness of `fs`.

## skip_take_range.rs (+ fail/)

`Skip<Take<Range>>`, a concrete instantiation of `skip_take.rs`. Stage S2: the nested generic-impl
predicate instances are emitted in discovery order, so `Take<Range>`'s instance is used before it
is defined; reordering the emitted definitions by hand
gives `unknown` on both sides.

## fail/map_index0.rs, fail/map_value.rs

Twins of `tests/ui/pass/creusot/map.rs` that the solver does not refute, so they cannot stand in
`tests/ui/fail/creusot/`:

- `map_index0.rs`: `Map::produces` relates every `visited[k]` to the first input `s[0]` instead of
  `s[k]`, which breaks `produces_trans`.
- `map_value.rs`: the call site claims the second item is `Some(11)`.

## probes/

One file per question asked while building the tracked cases, each self-contained (trait, adapter
and call site copied in). Not run by the ui harness.

- `range_call_direct.rs`, `range_call_quantified.rs`: a `Range` call site with the ensures spelled
  as a direct term versus a quantified sequence equal to a literal — the direct spelling is the one
  the tracked tests use.
- `take_call_none.rs`, `take_call_value.rs`, `take_law.rs`: the same question for a generic `Take<I>`.
- `decuple_range.rs`, `decuple_range_trusted_map.rs` (+ `fail/`): `decuple_range` with `map.rs`'s
  proof structure, the second with `Map`'s `next` and law bodies trusted (`loop {}`) instead of
  checked — earlier steps toward `tests/ui/pass/creusot/decuple_range.rs`.
- `skip_concat/`: the `Skip::produces` concatenated-form probes (call-site and no-invariant
  variants, sat and unsat) that led to `tests/ui/pass/creusot/skip.rs`'s form.
