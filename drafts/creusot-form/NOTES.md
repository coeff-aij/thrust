# Creusot-form drafts with Rust-syntax predicates and trait laws

Drafts, not tests: none carries a ui_test header. They are the probes behind the records in the
thrust-research repository under `experiments/` (`2026-09-25-creusot-map-rust-syntax`,
`2026-09-25-sequence-spelling-call-site`, `2026-09-27-b5-reflexivity-law`,
`2026-09-27-map-produces-creusot-proof`, `2026-09-27-map-ext-creusot-form`). Each file is self-contained: the
Creusot-form `Iterator` trait with `produces_refl` and `produces_trans` as `#[thrust_macros::law]`s,
the adapters with Rust-syntax `#[predicate]` bodies, and a call site.

Run one from the repository root with the PCSat wrapper and a CoAR built from fptprove develop
2493045c3 or later (earlier builds stall on native sequences). The `decuple_range` verdicts are on
this branch, which skips re-analyzing a generic callee's body at an instance whose contract has no
unknowns (a2d0e79); on main d5dc8e3 the trusted-`Map` pair times out on both sides:

```sh
THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=<image> THRUST_SOLVER_TIMEOUT_SECS=120 \
cargo run -- -Adead_code -C debug-assertions=off -A unused-variables drafts/creusot-form/<file>.rs
```

| File | Content | Verdict (fptprove develop 2493045c3 unless stated) |
| --- | --- | --- |
| `range_call_quantified.rs` | Range alone; `next`'s ensures quantify a sequence equal to a literal; one `next`, `assert!(matches!(first, Some(0)))` | timeout |
| `range_call_direct.rs` | the same with the literals as direct terms | sat, 16 s |
| `take_call_none.rs` | generic `Take<I>` over Range, direct spelling, `assert!(matches!(second, None))` | sat, 16 s |
| `take_call_value.rs` | the same with `assert!(matches!(first, Some(0)))` | timeout |
| `take_law.rs` | `Take<I>` with the two laws, both assertions | timeout |
| `map_creusot.rs` | Creusot's `Map` in Creusot's form (`produces` with an existential input sequence; `next_precondition`, `preservation`, `reinitialize`), laws, a `Range` call site with a partial closure | timeout at 120 s |
| `decuple_range.rs` | Creusot's `decuple_range` with its positional property `v[k] == 10 * k`: `map_creusot.rs`'s `Map` and `Range` with Creusot's `next` spec (singleton `produces`, no one-step ensures), `collect` / `from_iter` in the `produces` form; fail twin in `fail/` | timeout on both sides (1/1 each) |
| `decuple_range_trusted_map.rs` | the same with `Map`'s `next` and law bodies trusted (`loop {}`); fail twin in `fail/` | sat 15 s 4/4; fail Unsat 3/6 (31 to 39 s), timeout 3/6 |
| `map_creusot_lemmas.rs` | `map_creusot.rs`'s `Map` with Creusot's proof structure: `produces_one`, the ghost lemmas `produces_one_produces` and `produces_one_invariant` (split into one lemma per conjunct of the invariant, plus `produces_one_prefix`, the instance of `preservation` at `[e] ++ s`) called from `next` on ghost snapshots, and `produces_trans` through `produces_trans_split`; Creusot's `next` spec; the two-`next` call site | on fptprove develop 63e7b97e4: sat 3/3, 14 s |
| `fail/map_creusot_lemmas.rs` | the same, with `Map::produces` reading `s[0]` for every `visited[k]` (breaks `produces_trans`) | on 63e7b97e4: unknown 3/3 at 120 s (not refuted) |
| `fail/map_creusot_lemmas_value.rs` | the same, with the call site claiming `Some(11)` | on 63e7b97e4: unknown 3/3 at 120 s; with `Map`'s bodies trusted, timeout 3/3 |
| `decuple_range_lemmas.rs` | `decuple_range.rs` with the `Map` of `map_creusot_lemmas.rs`, fully checked | on 63e7b97e4: sat 3/3, 5.5 s |
| `fail/decuple_range_lemmas.rs` | the same, claiming `v[k] == 10 * k + 1` | on 63e7b97e4: unsat 3/3, 20 to 26 s |
| `map_ext_creusot.rs` | Creusot's `MapInv` (`iterators/map_ext.rs`) in its own form: the ghost history `produced` passed to an `Fn(Item, Ghost<Seq<Item>>)` closure, `produces` with the existential input sequence and the history `produced ++ s[..k]` at the `k`-th item, the invariant `reinitialize && preservation_inv && iter.invariant && next_precondition`, `completed` resetting `produced`; `map_creusot_lemmas.rs`'s proof structure; `Range { 1, 5 }` with `requires(x == produced.len() + 1)`, two `next`s | on fptprove develop d0a71c61c: no answer at 30 s 3/3, timeout 3/3 at 120 s; with `Map`'s bodies trusted sat 3/3; every body alone sat except `produces_trans_split` (no answer at 30 s 3/3) |
| `fail/map_ext_creusot_pre.rs` | the same, with the closure requiring `x == 1` (the history dropped) | on d0a71c61c: unsat 3/3, 19 to 20 s |
| `fail/map_ext_creusot_history.rs` | the same, with `next` not extending `produced` | on d0a71c61c: unsat 3/3, 22 s |
| `fail/map_ext_creusot_value.rs` | the same, with the call site claiming `Some(21)` | on d0a71c61c: no answer at 30 s 3/3, timeout 1/1 at 120 s |
| `skip_take.rs` | Creusot's `examples/skip_take` at a generic `I` (`Skip<Take<I>>`, `Range` call site); reflexivity only through the `produces_refl` law guarded by the invariant, `Skip::produces` in the concatenated form | on fptprove develop d34a33c44: sat 3/3, 61 s |
| `fail/skip_take_some.rs` | the same, with the call site claiming `Some` | on d34a33c44: unsat 3/3, 11 s |
| `fail/skip_take_take_count.rs` | the same, with `Take::produces` counting one item too many | on d34a33c44: unsat 3/3, 16 s |

The direct spelling of the ensures is the one the tracked tests use. The two frontend defects
these drafts exposed (a stuck `Model::Ty` projection, and closure contracts named per method)
are fixed in the commits that introduced `#[thrust_macros::law]`.
