# rustc coroutine `layout()` case study

The target is rustc's `rustc_abi::layout::coroutine` and its dependencies. `target.rs` is the
whole extraction in one file (`//@ignore-on-host`). The verified code lives in rustc's module
layout under `tests/rustc_coroutine/compiler/` (`rustc_hashes`, `rustc_index`, `rustc_abi`, one
crate of three modules), with the case study's own code (the iterator adapters of rewrites.md R8,
`SliceIter::find` of R9, `Model` declarations, std specifications, `Unwrap`, lemmas) under
`tests/rustc_coroutine/thrust/`. The goal is a proof that `layout()` does not panic.

Each file below is a crate root that includes the whole tree and selects one stage with
`#![thrust::verify_only(..)]`; functions outside the selection that have a contract are trusted.
The root also holds the stage's driver (`main` and the stubs of rewrites.md S5).
`tests/ui/fail/rustc_coroutine/<file>.rs` is its fail twin where one exists; it is the pass root
with the driver broken, regenerated and checked by `tests/rustc_coroutine/fail/check.sh`.

| file | selection | state |
| --- | --- | --- |
| `values.rs` | `rustc_hashes`, `rustc_abi` (lib.rs), `SliceIter` and its `find` | verified as stage file |
| `idx.rs` | `rustc_index::idx`, the own iterators `WordIter`, `SliceIter`, `IterEnumerated` | verified as stage file |
| `indexvec.rs` | `rustc_index::vec`, `rustc_index::slice`, the client `filled` | verified as stage file |
| `bitset.rs` | `rustc_index::bit_set` | verified as stage file |
| `simple.rs` | `rustc_abi::layout::simple` | draft, `ignore-on-host` |
| `univariant.rs` | `LayoutCalculator::univariant`, `univariant_biased` trusted on its contract | draft, `ignore-on-host`: no answer at 300 s, also for its panic obligations alone (query 17.8 MB) |
| `univariant_biased.rs` | `LayoutCalculator::univariant_biased` | draft, `ignore-on-host`: query about 323 MB |
| `eligibility.rs` | `coroutine_saved_local_eligibility` | draft, `ignore-on-host` |
| `layout.rs` | `layout()` and the adapters of `thrust/iter.rs` | draft, `ignore-on-host` |

The states are those of the single-file stage files; the module tree has not been run against
the solver yet.

The case study's iterators (`IdxRange`, `WordIter`, `BitIter`, `SliceIter`, `IterEnumerated`) and
the adapters of `thrust/iter.rs` implement std's `Iterator` and std.rs's `IteratorSpec`; `next` of
`IdxRange`, `WordIter` and `BitIter` carries a contract of its own, which refines the trait's.
The probes keep their own copy of Creusot's iterator trait.

`probes/` holds one small pass/fail pair per language feature the stages rely on (a `forall` over a
`Vec`, nested `Vec`s, an enum payload equality, an `Option` existential, a generic predicate in a
free function, a nested field, a `forall` in an invariant, the enumerate position over a bit-set iterator staying below the domain size, the length that the local `extend_from` and `collect_wrapped` give from the items the iterator produced, through the local `Map` and `Filter` adapters of layout.rs (rewrites.md R8), the closure precondition `Map` requires on every yielded item, the local `iter_all` requiring it too, and `max` through a `PartialOrdSpec` that states a struct's derived order), `probes/layout_call_site.rs`, rustc's call site establishing the dimension, matrix well-formedness and index conjuncts of `layout()`'s precondition, and `probes/permutation_split.rs`, `layout()`'s split of univariant's memory order over a generic `FieldIdx` with the counting lemmas of `thrust/lemmas.rs` (`ignore-on-host` until fptprove reads a forall function inside a `define-fun-rec`). `probes/nested_vec.rs`'s fail twin is
not refuted under native sequences.
