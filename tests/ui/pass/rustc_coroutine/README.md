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
| `bitset.rs` | set abstraction of DenseBitSet / BitMatrix / BitIter | verified |
| `eligibility.rs` | `coroutine_saved_local_eligibility` | full specification, no answer at 300 s, `ignore-on-host` |
| `univariant.rs` | trusted specification of `univariant` | draft, `ignore-on-host` |
| `layout.rs` | `layout()` integration | draft, `ignore-on-host` |

No stage file or probe uses std.rs's iterator specifications (`IteratorSpec`, `IntoIteratorSpec`
and the extern specs built on them): values.rs, eligibility.rs, layout.rs and the iterator probes
declare Creusot's iterator trait locally, as `tests/ui/pass/creusot/` does, and implement it for
their own iterators and adapters (rewrites.md R9).

`probes/` holds one small pass/fail pair per language feature the stages rely on (a `forall` over a
`Vec`, nested `Vec`s, an enum payload equality, an `Option` existential, a generic predicate in a
free function, a nested field, a `forall` in an invariant, the enumerate position over a bit-set iterator staying below the domain size, the length that the local `extend_from` and `collect_wrapped` give from the items the iterator produced, through the local `Map` and `Filter` adapters of layout.rs (rewrites.md R8), the closure precondition `Map` requires on every yielded item, the local `iter_all` requiring it too, and `max` through a `PartialOrdSpec` that states a struct's derived order), and `probes/layout_call_site.rs`, rustc's call site establishing the dimension, matrix well-formedness and index conjuncts of `layout()`'s precondition. `probes/nested_vec.rs`'s fail twin is
not refuted under native sequences.
