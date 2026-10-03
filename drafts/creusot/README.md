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

## counter_creusot (moved)

Creusot's `examples/counter` with its own property moved to the tracked suite:
`tests/ui/pass/creusot/counter_creusot.rs` and its fail twin `tests/ui/fail/creusot/counter_creusot.rs`.

## filter_creusot.rs (+ fail/)

Creusot's `Filter` (`examples/iterators/17_filter.rs` of creusot-rs/creusot 3620de437) in its own
form, with `Mapping<Int, Int>` as `Array<Int, Int>`. `next`'s loop invariant restates what Creusot
carries implicitly: the prophecy of the reborrow (`!s == !self.at_entry()`, as in `skip.rs`) and the
type invariant. Not yet verifiable: on fptprove 082cd295c the pass side is `unknown` at 70 s and the
fail twin times out at 300 s. With `next` trusted the `produces_trans` law alone gives no answer at
120 s; `map.rs` closes the same law with a lemma that names the joined witnesses.

## fold_map.rs

std's `Iterator::fold` with std's body, generic in the iterator, the accumulator and an `FnMut`
closure, specified in the form of Creusot's `Map` (`tests/ui/pass/creusot/map.rs`): the closure
states and accumulators along the produced items form a chain of call postconditions, the closure
may be called at every state the chain reaches, and the result ends the chain once the iterator is
completed. The client derives `result >= 0` from the chain. The loop invariant restates the
precondition, as the generic tests do, and holds the chain under an `exists`; the lemma
`fold_chain_push` extends it by one item and verifies alone. Not yet verifiable: on fptprove
082cd295c the program gives no answer (timeout at about 160 s, also with an empty `main`), and with
`fold` trusted the rest verifies. Ghost locals cannot carry the chain instead, since they are not
live at the loop header. A `MapInv`-style variant (the closure receives the ghost history of the
items so far) cannot be written either: `MapInv` keeps that history in a ghost field of its
struct, and `fold` has only locals to keep it in.

## try_fold_map.rs

std's `Iterator::try_fold` (`?` on each call, the `Try` type fixed to `Option<B>`, the iterator
taken as `&mut`) in the form of `fold_map.rs`: each chain step is a call returning `Some`; `Some(r)`
ends a chain over a completed iterator, `None` is a call returning `None` at the end of a chain.
Needs `THRUST_TRY_SPECS=1`. Same state as `fold_map.rs`: with `try_fold` trusted the rest verifies,
and the program gives no answer on fptprove 082cd295c (timeout at about 175 s, also with an empty
`main`).

## skip_take_range.rs (+ fail/)

`Skip<Take<Range>>`, a concrete instantiation of `skip_take.rs`. Stage S2: the nested generic-impl
predicate instances are emitted in discovery order, so `Take<Range>`'s instance is used before it
is defined; reordering the emitted definitions by hand
gives `unknown` on both sides.

## decuple_range_closure_inferred.rs (+ fail/)

`tests/ui/{pass,fail}/creusot/decuple_range.rs` with the closure's `requires(x < 100)` left to
inference. The closure's precondition unknown then sits under the quantifiers of
`Map::next_precondition` and `Map::preservation`, and so under a `forall` in the premises that
assume `Map::invariant`. On fptprove 0360cb142 both sides give no answer at 60 s, and at 300 s
the solver is killed for memory (6 GB and 8 GB) while normalizing the clauses, before its CEGIS
loop starts. With `requires(true)` written instead, both sides answer.

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
