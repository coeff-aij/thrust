# Creusot-form drafts with Rust-syntax predicates and trait laws

Drafts, not tests: none carries a ui_test header, and none is meant to pass today. They are the
probes behind the records in the thrust-research repository under `experiments/` dated 2026-09-25
(`creusot-map-rust-syntax`, `sequence-spelling-call-site`). Each file is self-contained: the
Creusot-form `Iterator` trait with `produces_refl` and `produces_trans` as `#[thrust_macros::law]`s,
the adapters with Rust-syntax `#[predicate]` bodies, and a call site.

Run one from the repository root with the PCSat wrapper and a CoAR built from fptprove develop
2493045c3 or later (earlier builds stall on native sequences):

```sh
THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=<image> THRUST_SOLVER_TIMEOUT_SECS=120 \
cargo run -- -Adead_code -C debug-assertions=off -A unused-variables drafts/creusot-form/<file>.rs
```

| File | Content | Verdict on fptprove develop 2493045c3 |
| --- | --- | --- |
| `range_call_quantified.rs` | Range alone; `next`'s ensures quantify a sequence equal to a literal; one `next`, `assert!(matches!(first, Some(0)))` | timeout |
| `range_call_direct.rs` | the same with the literals as direct terms | sat, 16 s |
| `take_call_none.rs` | generic `Take<I>` over Range, direct spelling, `assert!(matches!(second, None))` | sat, 16 s |
| `take_call_value.rs` | the same with `assert!(matches!(first, Some(0)))` | timeout |
| `take_law.rs` | `Take<I>` with the two laws, both assertions | timeout |
| `map_creusot.rs` | Creusot's `Map` in Creusot's form (`produces` with an existential input sequence; `next_precondition`, `preservation`, `reinitialize`), laws, a `Range` call site with a partial closure | timeout at 120 s |
| `decuple_range.rs` | Creusot's `decuple_range` with its positional property `v[k] == 10 * k`: `map_creusot.rs`'s `Map` and `Range` with Creusot's `next` spec (singleton `produces`, no one-step ensures), `collect` / `from_iter` in the `produces` form; fail twin in `fail/` | timeout (pending repeat) |
| `decuple_range_trusted_map.rs` | the same with `Map`'s `next` and law bodies trusted (`loop {}`); fail twin in `fail/` | sat 15 s 2/2, fail Unsat 33 s |

The direct spelling of the ensures is the one the tracked tests use. The two frontend defects
these drafts exposed (a stuck `Model::Ty` projection, and closure contracts named per method)
are fixed in the commits that introduced `#[thrust_macros::law]`.
