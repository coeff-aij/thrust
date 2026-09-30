# rustc coroutine `layout()` case study

The target is rustc's `rustc_abi::layout::coroutine` and its dependencies, copied into `target.rs`
with only annotations added (`//@ignore-on-host`: Thrust does not analyze the whole file yet). The
goal is a proof that `layout()` does not panic. Each stage file is one part of `target.rs`;
`tests/ui/fail/rustc_coroutine/<file>.rs` is its fail twin where one exists.

| file | content | state |
| --- | --- | --- |
| `values.rs` | Size / Align / Integer / Primitive / Scalar / Niche / TargetDataLayout | verified |
| `idx.rs` | the `Idx` trait, IdxRange and WordIter iterators | verified |
| `indexvec.rs` | IndexVec over a native sequence, trusted method contracts | verified |
| `bitset.rs` | set abstraction of DenseBitSet / BitMatrix / BitIter | pass side fails on `main` (a false alarm through `BitMatrix::rows` under native sequences) |
| `eligibility.rs` | `coroutine_saved_local_eligibility` | draft, `ignore-on-host` |
| `univariant.rs` | trusted specification of `univariant` | draft, `ignore-on-host` |
| `layout.rs` | `layout()` integration | draft, `ignore-on-host` |

`probes/` holds one small pass/fail pair per language feature the stages rely on (a `forall` over a
`Vec`, nested `Vec`s, an enum payload equality, an `Option` existential, a generic predicate in a
free function, a nested field, a `forall` in an invariant, the enumerate position over a bit-set iterator staying below the domain size), and `probes/layout_call_site.rs`, rustc's call site establishing the dimension and index conjuncts of `layout()`'s precondition. `probes/nested_vec.rs`'s fail twin is
not refuted under native sequences.
