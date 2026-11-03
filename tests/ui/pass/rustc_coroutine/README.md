# rustc coroutine `layout()` case study

The target is rustc's `rustc_abi::layout::coroutine` and its dependencies. `target.rs` is the
whole extraction in one file (`//@ignore-on-host`). The verified code lives in rustc's module
layout under `tests/rustc_coroutine/compiler/` (`rustc_hashes`, `rustc_index`, `rustc_abi`, one
crate of three modules), with the case study's own code (the iterator adapters of rewrites.md R8,
`Model` declarations, std specifications, lemmas) under
`tests/rustc_coroutine/thrust/`. The goal is a proof that `layout()` does not panic.

Each file below is a crate root that includes the whole tree and selects one part of rustc's code
with a `//@rustc-env: THRUST_VERIFY_ONLY=..` header: a module (`rustc_hashes`, the functions of
`rustc_abi`'s lib.rs, all of `rustc_index`), or one large function with the helpers a rewrite added
for it. Each rustc function is selected by one root; functions outside the selection that have a
contract are trusted. A function without a contract is checked only where a caller the analysis
reaches calls it; the roots that select a part of rustc's code and are not drafts split by goal
(`indexvec_int_range.rs`, a check of an option, does not), so
`THRUST_REPORT=functions` lists one that no such caller reaches as checked in no part.
The root also holds its driver (`main` and the stubs of rewrites.md S5); the root's own test
functions with a contract are selected with `crate`.
`tests/ui/fail/rustc_coroutine/<file>.rs` is its fail twin where one exists; it is the pass root
with the driver broken, regenerated and checked by `tests/rustc_coroutine/fail/check.sh`.
`hashes.rs` and `eligibility.rs` have no driver, and `eligibility.rs`'s function is private to
its module; `hashes.rs` has no fail twin. Its twin checks only
`set_assignment`, under `--cfg thrust_eligibility_fail`, which adds a contract the helper's
write refutes. It does not check the stage's own function, whose parts take about seven minutes.
`LocalIdx: Model<Ty: PartialEq>` on the stage function and on `make_ineligible` is a verification
bound on a type parameter, not a change to rustc's code: the proved `DenseBitSet::insert` requires it.

| file | selection | state |
| --- | --- | --- |
| `hashes.rs` | `rustc_hashes` | verified, each goal on its own (`THRUST_SPLIT_GOALS`); no analyzed code calls `Hash64::new` and `as_u64`, so their bodies are checked in no part |
| `values.rs` | `rustc_abi` (lib.rs) | verified, each goal on its own; `main` reveals `TargetDataLayout::pointer_space_ok` and `pointer_size_is`, which it reads (#132) |
| `index.rs` | `rustc_index::**` (`Idx`, `IndexVec`, `IndexSlice`, the bit sets, the own iterators `IdxRange`, `WordIter`, `SliceIter`, `IterEnumerated`), and `crate`: the clients `filled`, `two_members` and `column_bound` | verified, each goal on its own |
| `indexvec_int_range.rs` | `rustc_index::vec`, `rustc_index::slice`, `filled`, under `THRUST_INT_RANGE=conversions` | verified; a check of the option, not a run of the case study: with it `count_ones` of bit_set.rs has no specification of `sum` |
| `simple.rs` | `rustc_abi::layout::simple` | draft, `ignore-on-host` |
| `univariant.rs` | `LayoutCalculator::univariant`, `univariant_biased` trusted on its contract | verified, one part per goal (`THRUST_SPLIT_GOALS`), with the predicates its contracts pass on unchanged `#[thrust::opaque]`: `fits_in_any_order`, `weighs`, `unsized_misplaced`, `some_field_niche` (layout.rs), `Primitive::size_in`, `FieldsShape::arbitrary_of`, `TargetDataLayout::pointer_space_ok`, `TargetDataLayout::pointer_size_is` (lib.rs); `univariant_biased`, `Primitive::size`, `layout()`, `pointer_size_in` and `pointer_align_in` reveal those they read (#132) |
| `univariant_biased.rs` | `LayoutCalculator::univariant_biased` | draft, `ignore-on-host`: its query (58.7 MB) is killed for memory with 16 GB (#133) |
| `eligibility.rs` | `coroutine_saved_local_eligibility` and the helpers `make_ineligible` and `set_assignment`, which hold its writes to `assignments` | verified, each goal on its own (`THRUST_SPLIT_GOALS`) |
| `layout.rs` | `layout()` and the adapters of `thrust/iter.rs`; the lemmas of `thrust/lemmas.rs` assumed | draft, `ignore-on-host` |
| `lemmas.rs` | the counting lemmas of `thrust/lemmas.rs` that `layout()` uses | verified |

The roots that are not drafts answer over the module tree in the ui suite; the states of the
drafts are those of the single-file stage files.

The case study's iterators (`IdxRange`, `WordIter`, `BitIter`, `SliceIter`, `IterEnumerated`) and
the adapters of `thrust/iter.rs` implement std's `Iterator` and std.rs's `IteratorSpec`; `next` of
`IdxRange`, `WordIter` and `BitIter` carries a contract of its own, which refines the trait's.
The probes keep their own copy of Creusot's iterator trait.

`probes/` holds one small pass/fail pair per language feature the stages rely on (a `forall` over a
`Vec`, nested `Vec`s, an enum payload equality, an `Option` existential, a generic predicate in a
free function, the layout a generic `Deref` gives through `post!` and the requirement that its
`deref` is a function (`deref_functional`), the local `u64::wrapping_add` spec on a wrapping and
a small sum, a nested field, a `forall` in an invariant, the enumerate position over a bit-set iterator staying below the domain size, the length that the local `extend_from` and `collect_wrapped` give from the items the iterator produced, through the local `Map` and `Filter` adapters of layout.rs (rewrites.md R8), the closure precondition `Map` requires on every yielded item, the local `iter_all` requiring it too, and `max` through a `PartialOrdSpec` that states a struct's derived order), `probes/layout_call_site.rs`, one instance of rustc's call site (two saved locals) satisfying the dimension, matrix well-formedness and index conjuncts of `layout()`'s precondition, and `probes/permutation_split.rs`, `layout()`'s split of univariant's memory order over a generic `FieldIdx` with a copy of the counting lemmas of `thrust/lemmas.rs` over `Vec`, which the `lemmas.rs` root verifies in place, and `probes/size_arithmetic.rs`, the size arithmetic of `univariant_biased` (`align_to`, `checked_add` against the object size bound, the niche's move by the field's offset) with the contracts that the case study's `Align::bytes`, `Size::align_to`, `obj_size_bound` and `Size::checked_add` lack, a draft whose loop goals get no answer; its fail twin, which verifies only `field_niche_placed`, is refuted without the niche offset's bound. `probes/nested_vec.rs`'s fail twin is
not refuted under native sequences.
