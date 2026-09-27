# Creusot benchmark drafts

What does not verify yet, and non-refuting fail twins, for the benchmark cases tracked under
`tests/ui/{pass,fail}/creusot/`. Full verdict tables and history are in `drafts/creusot-form/NOTES.md`
and `drafts/creusot-examples/NOTES.md` as of commit 382af70, before this directory replaced them.

## map_ext.rs

Creusot's `MapInv` (the ninth adapter, `iterators/map_ext.rs`) in Creusot's own form: the ghost
history `produced`, `produces` with an existential input sequence, and `map.rs`'s proof structure
extended with `history_split` and `produces_trans_witness`. Stage S3: every body checks alone
except `produces_trans_witness`'s `produces` conclusion (the existential witness), which stalls.

- `fail/map_ext_pre.rs`: the closure requires `x == 1` (drops the history) — refutes.
- `fail/map_ext_history.rs`: `next` does not extend `produced` — refutes.
- `fail/map_ext_value.rs`: the call site claims `Some(21)` — not re-measured since the two new
  lemmas were added.

## skip_take_range.rs (+ fail/)

`Skip<Take<Range>>`, a concrete instantiation of `skip_take.rs`. Stage S2: the nested generic-impl
predicate instances are emitted in discovery order, so `Take<Range>`'s instance is used before it
is defined (B9 in the thrust-research status note); reordering the emitted definitions by hand
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
