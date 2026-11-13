# rustc coroutine `layout()` case study

The target is rustc's `rustc_abi::layout::coroutine` and its dependencies. `target.rs` is the
whole extraction in one file (`//@ignore-on-host`). The verified code lives in rustc's module
layout under `tests/rustc_coroutine/compiler/` (`rustc_hashes`, `rustc_index`, `rustc_abi`, one
crate of three modules), with the case study's own code (the iterator adapters of rewrites.md R8,
`Model` declarations, std specifications, lemmas) under
`tests/rustc_coroutine/thrust/`. The goal is a proof that `layout()` does not panic. The module
tree is meant to keep the smallest part of rustc's code that compiles with `layout()`: an item nothing
needs in order to compile is dropped, also where `target.rs` still has it.

`cargo test --test ui` skips these roots and their twins in `tests/ui/fail/rustc_coroutine/` and the probes under `probes/` unless `THRUST_UI_CASE_STUDY=1`; the evaluation's scripts run them by path.

Each file below is a crate root that includes the whole tree and selects one part of rustc's code
with a `//@rustc-env: THRUST_VERIFY_ONLY=..` header: a module (`rustc_hashes`, the functions of
`rustc_abi`'s lib.rs, all of `rustc_index`), or one large function with the helpers a rewrite added
for it. Each rustc function is in the part one root selects; functions outside the selection that
have a contract are trusted. A root also selects the functions through which code outside its
selection enters a function whose contract is inferred (`Size::unsigned_int_max`, entered through
`Niche::available`): at such an entry Thrust would fix the precondition to `true`, and the function
panics on overflow. Such a function is checked again in each root that selects it; `available` is
selected so in `scalar_pair.rs`, `place_field.rs` and `probes/size_arithmetic.rs`. A function
without a contract is checked only where a caller the analysis reaches calls it; the roots that select a part of rustc's code and are not drafts split by goal
(`indexvec_int_range.rs`, a check of an option, splits only into the classes of clauses that
share no unknown, `THRUST_SPLIT`), so
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
So are `VariantIdx: Model<Ty: PartialEq>` and `Cx: Model<Ty: PartialEq>` on `univariant` and
`univariant_biased`, which `scalar_pair`'s contract needs.
`layout.rs`'s fail twin defines property 3 at the promoted fields, `ineligible_promoted`, as `true` (`--cfg thrust_layout_fail`),
and each of its `assume!`s has a reachability root, `layout_reach_<name>.rs`
(`--cfg thrust_layout_reach_<name>`), with a `proof_assert!(false)` right after the `assume!`: a
refutation shows that the assumption leaves the path after it reachable. The fallback's
assumptions (below) share one, `layout_reach_fallback.rs`, with a `proof_assert!(false)` after the
last assumption in `layout()`. At 54459771, with fptprove ce3cea65b at 300 s, with and without
cvc5 1.4.1, `layout_reach_pair.rs` is refuted. The target parts of `layout_reach_prefix.rs`
(`unknown`), `layout_reach_variant.rs` (timeout) and `layout_reach_fallback.rs` get no answer:
the latter's target in `layout()` times out. So the goals after those assumptions are not
shown to hold non-vacuously.
`univariant_biased.rs`'s `assume!`s, and its calls of the fallback's wrappers in `thrust/iter.rs`
and `thrust/assumed_requires.rs`, likewise each have a reachability root, `univariant_biased_reach_<name>.rs`
(`--cfg thrust_univariant_biased_reach="<name>"`). On f25eb5e0, with fptprove 27431dba0 at 300 s and
16 GB, solving the parts each twin adds to the pass root's (the goal of its `proof_assert!`), three
of the eleven are refuted: `largest_niche`, `alignment_group_key` and `variant_index`; the other
eight get no answer. So the goals after those eight points are not shown to hold non-vacuously.
A twin after a call of a wrapper of `thrust/iter.rs` or
`thrust/assumed_requires.rs` shows the path reachable under the wrapper's `ensures`, not that the `requires` it
assumes holds at the call.

| file | selection | state |
| --- | --- | --- |
| `hashes.rs` | `rustc_hashes` | verified, each goal on its own (`THRUST_SPLIT_GOALS`); `Hash64::new` is checked where `scalar_pair` calls it, in the `scalar_pair.rs` root |
| `values.rs` | `rustc_abi` (lib.rs) | verified, each goal on its own; `main` reveals `TargetDataLayout::pointer_space_ok` and `pointer_size_is`, which it reads (#132) |
| `index.rs` | `rustc_index::**` (`Idx`, `IndexVec`, `IndexSlice`, the bit sets, the own iterators `IdxRange`, `WordIter`, `IterEnumerated`), and `crate`: the clients `filled`, `two_members` and `column_bound` | verified, each goal on its own |
| `indexvec_int_range.rs` | `rustc_index::vec`, the functions of `rustc_index::slice` but `IterEnumerated::yields_last` (assumed on its contract, which `index.rs` checks; under this option its goal gets no answer), `filled`, under `THRUST_INT_RANGE=conversions` | verified, each class of clauses on its own (`THRUST_SPLIT`); a check of the option, not a run of the case study: with it `count_ones` of bit_set.rs has no specification of `sum` |
| `simple.rs` | `crate`: `drive`, which reads `LayoutData::scalar_pair`'s fields as `univariant_biased` does; `scalar_pair` assumed on its contract, which the `scalar_pair.rs` root checks | verified |
| `scalar_pair.rs` | `LayoutData::scalar_pair` (layout/simple.rs), with std's `Iterator::max_by_key` on std.rs's contract; `Niche::from_scalar` and `Scalar::size` assumed on their contracts, which `values.rs` checks | verified, each goal on its own (`THRUST_SPLIT_GOALS`); the fail twin asserts, before the niches are computed, that the second scalar is placed at 0, and false after a call of `max_by_key` on a chain of two concrete options (`drive_max_by_key`), which shows the code after such a call reachable under its contract for `u32` items; that it is reachable for `scalar_pair`'s `Niche` items is inferred from this, not run |
| `univariant.rs` | `LayoutCalculator::univariant`, `univariant_biased` trusted on its contract | verified, one part per goal (`THRUST_SPLIT_GOALS`), with the predicates its contracts pass on unchanged `#[thrust::opaque]`: `layout_pre`, which `univariant`'s body reveals, `fits_in_any_order`, `weighs`, `unsized_misplaced`, `some_field_niche` (layout.rs), `Primitive::size_in`, `FieldsShape::arbitrary_of`, `TargetDataLayout::pointer_space_ok`, `TargetDataLayout::pointer_size_is` (lib.rs); `univariant_biased`, `Primitive::size`, `layout()`, `pointer_size_in` and `pointer_align_in` reveal those they read (#132) |
| `univariant_biased.rs` | `LayoutCalculator::univariant_biased`, with the field loop in `place_fields` (rewrites.md R19) and `univariant_biased_place` (the `place_fields` call, the size check and the `Ok` of the layout) trusted on their contracts, `univariant_biased_finish` and `backend_repr_of` (the code after the size check), and the fallback's wrappers of `thrust/iter.rs` (`map_new_assumed`) and `thrust/assumed_requires.rs` | verified under its fallback, each goal on its own, its functional contract trusted on `univariant_biased_place` (below) (`THRUST_SPLIT_GOALS`, `THRUST_CALL_RESULT_DIRECT`): `assume!`s of the goals the solver does not answer, the wrappers of `thrust/iter.rs` (`map_new_assumed`) and `thrust/assumed_requires.rs` (the others) whose bodies assume a callee's `requires` where an `assume!` at the call cannot name the closure's type (`map_new_assumed`, `filter_new_assumed`, `filter_next_assumed`, `map_or_assumed`, `sort_by_key_assumed`), and one trusted helper, `arbitrary_parts` of layout.rs, the match on a scalar pair's fields; `iter_enumerated_trusted` of `thrust/iter.rs` and `as_local` (`result == x`) are checked against their contracts. Its postcondition is one opaque predicate, `univariant_biased_post`, the conjunction of the nine conjuncts `univariant` reads, which `univariant_biased_place` and `univariant` reveal; it rests on `univariant_biased_place`'s trusted contract, which ensures the same predicate under `order_ok`, which the root proves at the call. What the root checks of `univariant_biased` is the code before the call (the field order, the sort keys and that the order is a permutation), and `univariant_biased_finish` and `backend_repr_of`, whose `requires` that `offsets` has as many entries as the fields only `univariant_biased_place`'s trusted body establishes: `univariant_biased` ends with the call of `univariant_biased_place`, so its goal reads the callee's postcondition through one unknown, which the solver answers for the one atom and not for the nine conjuncts. `univariant_biased_place`'s own postcondition needs the witness of `weighs`'s existential (#278, #288). With fptprove 28eaca8b6a at 300 s a part, six at a time, its 129 parts are `sat`, the slowest in 253 s (with cvc5 1.4.1); two parts take about 220 s alone in this root, so one of them can exceed 300 s with six at once |
| `place_field.rs` | `LayoutCalculator::place_field`, the field loop's body after the unsized checks (rewrites.md R18), with its helpers `align_step` (the padding and the alignment), `set_offset` (the write of the offset) and `offer_niche` (the niche choice), and the lemmas `pow2_mono`, `bytes_within`, `shl_is_pow2`, `pow2_pos`, `aligned_within` and `niche_ends_later` | verified, each goal on its own (`THRUST_SPLIT_GOALS`) |
| `permutation_sum.rs` | the lemmas of layout.rs that bound the weight of the fields placed first in memory order by the weight of all the fields, over the counting functions of `thrust/lemmas.rs`: `sum_at_le` and the inductions it uses (`sum_occurring_step`, `sum_at_occurring`, `sum_occurring_le`) | draft, `ignore-on-host`: of its 38 goals, the three induction steps of `sum_occurring_step` and `sum_at_occurring`, stated for every weight sequence, are killed for memory and the rest are `sat`; its fail twin, `sum_at_le` without distinct indices, is refuted |
| `place_fields.rs` | `LayoutCalculator::place_fields`, `univariant_biased`'s field loop (rewrites.md R19), with its invariant over the loop's history, the lemmas `niche_sized` and `no_niche_ends_by`; `BackendRepr::is_unsized` and `LayoutData::is_unsized`, whose contracts state their bodies and which `values.rs` checks, `place_field` and the lemmas of `permutation_sum.rs` trusted on their contracts | draft, `ignore-on-host`: 17 of its 23 goals are `sat`; at 300 s the invariant at the loop's entry and two of the five goals of the loop body's paths (its back edge and its returns) are killed at the solver's 8 GB, and the other three get no answer; its fail twin is not refuted (no answer) |
| `eligibility.rs` | `coroutine_saved_local_eligibility` and the helpers `make_ineligible` and `set_assignment`, which hold its writes to `assignments` | verified, each goal on its own (`THRUST_SPLIT_GOALS`) |
| `layout.rs` | `layout()`, its helpers and lemmas in `coroutine.rs`, the adapters of `thrust/iter.rs`, and the lemmas of `thrust/counts.rs` that take the per-variant `Map` and `Filter` (`filter_count`, `filter_yields_below`, `filter_selects`, `filter_selects_all`, `filter_covers_passed`, `filter_rejects_rest`, `map_count_exact`, `map_selected_entries`) and `IterEnumerated::yields_last`; the lemmas of `thrust/lemmas.rs`, the other lemmas of `thrust/counts.rs` and the count lemmas of `coroutine.rs` assumed | verified under its fallback but for one goal, each goal on its own (`THRUST_SPLIT_GOALS`): three `assume!`s, and as the fallback one call through a checked wrapper whose body assumes the callee's precondition: `map_new_assumed` of `thrust/iter.rs`, for `Map::new` over the variants, whose precondition an `assume!` at the call cannot state. With fptprove 28eaca8b6a and cvc5 1.4.1 at 300 s a part, six at a time, its 349 parts are `sat` (the slowest in 204 s); without cvc5, parts of `variant_layout` and `variant_field_layouts` give no answer. The goals hold under assumptions not all shown to leave their paths reachable (above); its fail twin is refuted (four goals of `combine_offsets`' closure `unsat`). The per-variant closure's `requires` at every variant and closure state the map reaches (the variants' `Map`'s `inv`) is assumed, by `map_new_assumed`, and not verified (the `collect` over the variants takes it from `map_new_assumed`'s `ensures`); as that assumption sits in the wrapper's body, `layout_reach_fallback.rs`'s twin in `layout()` cannot show it satisfiable at this closure |
| `lemmas.rs` | the counting lemmas of `thrust/lemmas.rs`: the permutation split that `layout()` uses and its upper bound (`permutation_split_le`), and the pigeonhole principle (`every_index_occurs`) that `univariant_biased` uses | verified |
| `counts.rs` | the count and the weight of a variant's fields, `thrust/counts.rs`, which `layout()`'s per-variant closure uses (the count), and `coroutine.rs`'s `ones_assigned_disjoint`, `ones_step` and `card_ones` (the ineligible set and the locals Assigned to one variant are at most the locals) | draft, `ignore-on-host`: the lemmas over the field list (with `map_bound`, the bound of `Filter`'s index map by a count, and `map_exact`, its equality for a whole selection), the weighted ones and `filter_yields_below` verify; the step of `ones_assigned_disjoint` (through the bit arithmetic of `ones`, which `ones_step` alone answers) and the lemmas over the per-variant `Map` and `Filter` get no answer; `layout.rs` selects those lemmas and checks the `ensures` of `filter_count`, `map_count_exact` and `map_selected_entries` with a `proof_assert!` |
| `filter.rs` | `thrust/iter.rs`'s `Filter`, which `layout()` calls: its `next` against the contract that the item it returns is the last the inner iterator produced, and its `IteratorSpec` laws | verified, each goal on its own (`THRUST_SPLIT_GOALS`) |

The roots that are not drafts answer over the module tree in the ui suite; the states of the
drafts are those of the single-file stage files.

The case study's iterators (`IdxRange`, `WordIter`, `BitIter`, `IterEnumerated`) and the adapters
of `thrust/iter.rs` implement std's `Iterator` and std.rs's `IteratorSpec`; `IndexSlice::iter`
returns std's `slice::Iter`, as rustc's does; `next` of
`IdxRange`, `WordIter` and `BitIter` carries a contract of its own, which refines the trait's.
The probes keep their own copy of Creusot's iterator trait, except `probes/field_closures.rs`,
which uses std.rs's `IteratorSpec` and copies of the adapters of `thrust/iter.rs`.

`probes/` holds one small pass/fail pair per language feature the stages rely on (a `forall` over a
`Vec`, nested `Vec`s, an enum payload equality, an `Option` existential, a generic predicate in a
free function, the layout a generic `Deref` gives through `post!` and the requirement that its
`deref` is a function (`deref_functional`), the local `u64::wrapping_add` spec on a wrapping and
a small sum, a nested field, a `forall` in an invariant, the enumerate position over a bit-set iterator staying below the domain size, the length that the local `extend_from` and `collect_wrapped` give from the items the iterator produced, through the local `Map` and `Filter` adapters of layout.rs (rewrites.md R8), the closure precondition `Map` requires on every yielded item, the local `iter_all` requiring it too, and `max` through a `PartialOrdSpec` that states a struct's derived order), `probes/field_closures.rs`, `univariant_biased`'s closures over the fields (the two `Map`s over the fields without the tail and the `Filter` of the non-ZST fields over `iter_enumerated`, whose items index the offsets and give the scalars paired), with `Filter::next` stating that the item it returns is the inner iterator's, as `thrust/iter.rs`'s `Filter` now does, `probes/layout_call_site.rs`, one instance of rustc's call site (two saved locals) satisfying the dimension, matrix well-formedness and index conjuncts of `layout()`'s precondition, and `probes/permutation_split.rs`, `layout()`'s split of univariant's memory order over a generic `FieldIdx` with a copy of the counting lemmas of `thrust/lemmas.rs` over `Vec`, which the `lemmas.rs` root verifies in place, `probes/sort_permutation.rs`, `univariant_biased`'s two `sort_by_key` calls on the first `end` entries of the identity memory order, whose result is a permutation of the fields (`arbitrary_of`) that `invert_bijective_mapping` takes, with written contracts (`closure!`) on the key closures and `alignment_group_key`, and `probes/call_result_chain.rs`, the path of `univariant_biased` from `data_layout()` to `obj_size_bound()` that places the fields, whose requirements on the data layout pass through every call result's unknown (issue #163): it verifies with the loop's invariant written and its body in `place_field`, a function with a checked contract; and `probes/size_arithmetic.rs`, the size arithmetic of `univariant_biased` (`align_to`, `checked_add` against the object size bound, the niche's move by the field's offset) with its own copies of the contracts that the case study's `Align::bytes`, `Size::align_to`, `obj_size_bound` and `Size::checked_add` state, a draft in which 11 goals get no answer, among them `offer_niche`'s `requires` of `niche.offset += offset` and the step of the lemma `sum_first_mono`; its fail twin, which verifies only `field_niche_placed`, is refuted without the niche offset's bound. `probes/nested_vec.rs`'s fail twin is
not refuted under native sequences.
