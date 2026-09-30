# Block encoding: query size of long block chains

Probes for the question of which basic blocks get a predicate and which arguments it carries,
raised by a derived `PartialEq::eq` on a wide struct. Nothing here is a feature; the design note
that uses these measurements decides what, if anything, changes.

## Files

- `derived_partialeq_wide_sat.rs`: the 18-field struct of fptprove `thrust-benchmarks` 79ab22edf,
  `benchmarks/DQpCSP/thrust_generated/unsolved/derived_partialeq_wide_struct_2026-09-30/`.
  `derived_partialeq_wide_unsat.rs` is its fail twin: the last field of the second value differs.
- `gen_wide_eq.py KIND N [--fail]`: a struct of N fields with a derived `PartialEq` and a `main`
  asserting two equal values equal. `mix` cycles `u64`, `usize`, a 3-variant enum and a 2-field
  struct (at N = 30 it prints fptprove's `mix30_sat.rs` byte for byte); `u64` uses `u64` only.
- `emit.sh TREE FILE OUT [EDITION]`: writes the query of one file without solving it, in the form
  the PCSat tests use (`THRUST_SOLVER=true`, a command other than `z3`).
- `query_size.py FILE...`: bytes without comments, clauses, predicates, predicate arity and the
  variables each clause quantifies, both as declared and as scalar leaves with tuple datatypes
  flattened. `--list` names the measures without reading the files; `--preds FILE` lists each
  predicate.
- `solve.sh FILE [SECS] [IMAGE]`: one PCSat run of an emitted query, 2 CPUs, 3 GB.

## The probes

Two switches in `needs_own_precondition`, both reverted by f3741ad; build 0949e4f, which has both,
to rerun them. Unset, 0949e4f emits what `main` b3ed4f1 emits.

- c820fc5, `THRUST_PROBE_EVERY_BLOCK_PREDICATE=1`: every block gets its own predicate, as before
  3019027.
- 0949e4f, `THRUST_PROBE_CHAIN_CUT=N`: a block with one incoming edge also gets one once N
  blocks have been merged since the nearest block with a predicate.

```sh
python3 drafts/block-encoding/gen_wide_eq.py mix 30 > /path/mix_30.rs
drafts/block-encoding/emit.sh . /path/mix_30.rs /path/cur
THRUST_PROBE_CHAIN_CUT=8 drafts/block-encoding/emit.sh . /path/mix_30.rs /path/cut8
python3 drafts/block-encoding/query_size.py /path/{cur,cut8}/thrust_output.smt2
```

The 18-field files were emitted with `THRUST_TRY_SPECS=1` and edition 2024, as in fptprove's
README; the generated files with neither.
