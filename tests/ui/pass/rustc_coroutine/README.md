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

Most roots are generated from the call graph of `layout()`, so that every function it reaches is
selected by a root. A generated root is a crate root that includes the whole tree and selects part
of rustc's code with a `//@rustc-env: THRUST_VERIFY_ONLY=..` header; its first comment line starts
with `// Generated root:`, and it is not edited by hand. A reached function of at least 40 lines
of code has a root of its own, named after it (`layout.rs`, `univariant.rs`,
`univariant_biased.rs`, `coroutine_saved_local_eligibility.rs`). Every other reached function (a
helper, a lemma, a small function, a stand-in for std that the case study writes) is selected by
the root of its row and module, `<row>_<module>_helpers.rs`, with the row of Table 5 it counts in
(`rustc_hashes`, `rustc_abi`, `rustc_index`, `univariant`, `univariant_biased`, `layout`, or
`standins` for a stand-in). The other header lines of a root (edition, flags, solver timeout,
split settings) are those its functions had in the hand-written roots the generated ones replaced; a row
and module whose functions had different settings has one root per setting, named after the earlier root. A function that has no body a root can check (a
declaration, a trusted or an ignored function, one kept only so that the code compiles) is not
selected. Each rustc function is in the part one root selects; functions outside the selection that
have a contract are trusted.

The reached set is closed under two rules, since a function can be checked without a call that names it:
every impl of a reached trait method (a call through a type parameter names the trait's declaration) and the rest of that
trait, and every law proof, lemma, helper and specification of a verified function (`extern_spec_fn`) of a reached type,
impl or module (a law proof proves a contract of the trait its type implements and no function calls it); a root also selects the laws its impls inherit from their traits (`<impl>::<law>`).
A function whose contract Thrust infers is selected in the root of each of its callers.

The roots written by hand stay where a generated root cannot say what they check; each keeps its
header and selection, and a generated root checks the bodies they leave out:
`index.rs` (the callers `filled`, `two_members` and `column_bound`, selected as `crate`, which call
the contracts of rustc_index, with `IndexVec` and `IndexSlice::index`, which a function pointer the driver hands to `deref` and the read `read_entry` need analyzed), `lemmas.rs` (`split`, the caller of the counting lemmas),
`scalar_pair.rs` (`LayoutData::scalar_pair` with the driver `drive_max_by_key` that hands `max_by_key`
a function pointer, and `Niche::available` its callee), `simple.rs` (`drive`, the caller of
`scalar_pair`'s contract), `univariant_caller.rs` (`univariant` with `univariant_biased` trusted on
its contract, and its driver), `indexvec_int_range.rs` (a check of `THRUST_INT_RANGE=conversions` on
`IndexVec` and `IndexSlice`, with its caller `filled`) and `weights.rs` (the weight lemmas, which
`layout()` does not reach). They also check functions a generated root selects.

A function without a contract is checked only where a caller the analysis reaches calls it; the roots that select a part of rustc's code and are not drafts split by goal
(`indexvec_int_range.rs`, a check of an option, splits only into the classes of clauses that
share no unknown, `THRUST_SPLIT`), so
`THRUST_REPORT=functions` lists one that no such caller reaches as checked in no part.
A caller root also holds its driver (`main` and the stubs of rewrites.md S5).
`tests/ui/fail/rustc_coroutine/<file>.rs` is a fail twin where one exists; it is a pass root
with a patch applied (the proof or the driver broken), regenerated and checked by
`tests/rustc_coroutine/fail/check.sh` from the root the patch names. The twin of `coroutine_saved_local_eligibility.rs` sets `--cfg thrust_eligibility_fail`, under
which the block contract of the last loop's write to `assignments` says what the write refutes.
`LocalIdx: Model<Ty: PartialEq>` on the stage function is a verification
bound on a type parameter, not a change to rustc's code: the proved `DenseBitSet::insert` requires it.
So are `VariantIdx: Model<Ty: PartialEq>` and `Cx: Model<Ty: PartialEq>` on `univariant` and
`univariant_biased`, which `scalar_pair`'s contract needs.
`layout.rs`'s fail twin defines property 3 at the promoted fields, `ineligible_promoted`, as `true` (`--cfg thrust_layout_fail`),
and each of its `assume!`s has a reachability root, `layout_reach_<name>.rs`
(`--cfg thrust_layout_reach_<name>`), with a `proof_assert!(false)` right after the `assume!`: a
refutation shows that the assumption leaves the path after it reachable. The fallback's
assumptions (below) share one, `layout_reach_fallback.rs`, with a `proof_assert!(false)` after the
last assumption in `layout()`. `layout_reach_pair.rs` follows the `proof_assert!` that replaced the
pair's `assume!`; with fptprove e74f0750b at 300 s its target is `unsat`, so the closure's
`requires`, which proves the pair, leaves the path after it reachable. At 54459771, with fptprove ce3cea65b at 300 s, with and without cvc5 1.4.1, the target parts of `layout_reach_prefix.rs`
(`unknown`), `layout_reach_variant.rs` (timeout) and `layout_reach_fallback.rs` get no answer:
the latter's target in `layout()` times out. So the goals after those assumptions are not
shown to hold non-vacuously.
Seventeen of `univariant_biased.rs`'s goals are `proof_assert!`s that were `assume!`s or a wrapper's
assumption: the index bounds `offsets[i]` and `offsets[j]` of the pair step (layout.rs 1311, 1312),
`scalar_pair`'s `requires` on the ordered pair (1267), `offsets[j]` of the condition (1301), the
`requires` of the first two `map_or` calls (892, 908), the sort's over its key closure (959), the third `map_or`'s (933, `niche.map_or(0, end_offset_of_niche)`), `iter_enumerated`'s (the field count passes `can_new`), `offsets[i]` of the condition, `VariantIdx::new(0)`'s, and those of `Filter::new` (1201) and of its
three `next` calls (1210, 1216, 1222), and `Map::new`'s for `largest_niche_size` (below); the last six are `sat` with fptprove e74f0750b within 300 s a
part (the parts holding each goal, solved once); the five proved last add six parts (two for the third `map_or`, one for each other), all `sat` with fptprove 16064279f at 300 s a part: 29 s for each of the `map_or` parts, 134 s for `offsets[i]`, within 2 s for the others. The
`assume!`s left are listed in the table's `univariant_biased.rs` row.
`Map::new`'s `requires` for `largest_niche_size` (the block at layout.rs 849) is proved in a block contract:
`requires` (`layout_pre`, `dl_of`, and the formula's closure and iterator facts), the lemma call
`fields_ok_of_layout_pre`, the lemma call `Map::preservation_inv_of_stable_closure` (thrust/iter.rs), and
`ensures` of the site's formula; the block scopes the lemma call because calling it at the start of
`univariant_biased` changes 99 other parts. `preservation_inv_of_stable_closure` gives `Map`'s `preservation_inv`
from the closure's `requires` at the last item of every produced sequence and from the closure's history invariant
keeping its precondition; the other law it needs, a call ends in a state `hist_inv!` allows (Creusot's
`postcondition_mut_hist_inv`), Thrust gives for a closure type parameter. With fptprove 16064279f (PR #377), at 60 s a part, 2 CPUs and 6 GB:
the 38 parts of `univariant_biased.rs` that change against fork main 81a956bb are all `sat`, and the lemma's 44 parts
(`THRUST_VERIFY_ONLY=case_study::iter::Map::preservation_inv_of_stable_closure` with this root's header;
`univariant_biased.rs` takes the lemma on its contract, and `standins_case_study_iter_helpers_layout.rs` checks it) are all `sat`.
The remaining `assume!`s of `univariant_biased.rs` each have a reachability root, `univariant_biased_reach_<name>.rs`
(`--cfg thrust_univariant_biased_reach="<name>"`). On f25eb5e0, with fptprove 27431dba0 at 300 s and
16 GB, solving the parts each twin adds to the pass root's (the goal of its `proof_assert!`), three
of the ten are refuted: `largest_niche`, `alignment_group_key` and `variant_index`; the other
seven get no answer. The twins `map_or`, `iter_enumerated` and `variant_index` are removed with their `assume!`s.
`largest_niche`'s point now follows the proof of `Map::new`'s `requires` (PR #377): with fptprove 16064279f at 60 s, of the 36 parts of
the twin that change against fork main 81a956bb, 35 are `sat` and one is `unsat` (part 80, 23 s), the goal of its `proof_assert!(false)` (layout.rs 880), the only `unsat` part (the pass root has none), so it stays refuted; the goal is `unsat` on main too (part 63, 22 s).
The `map` twin's 38 changed parts are all `sat`: it is unaffected by the change, and stays unanswered at f25eb5e0.
So the goals after the other points are not shown to hold non-vacuously.
The twins `pair`, `scalar_pair` and `pair_condition` follow goals that are `proof_assert!`s.
With fptprove develop 2f4da5e8f1 (cvc5 1.4.1), 4 CPUs per container, four parts at a time, at 300 s: `alignment_group_key` is refuted (part 42 of 154 `Unsat`) and another part times out, so its ui test, which expects only `Unsat`, fails on that part; `arbitrary` gives no answer (part 109 of 145 `Timeout`), so the unreachable-arm `proof_assert!` after `scalar_pair` is shown to hold but its path is not shown reachable.
The probes `probes/arbitrary_parts.rs` (`arbitrary_parts` alone) and `probes/univariant_biased_place.rs` (the body of `univariant_biased_place` and the lemma `fields_ok_of_layout_pre`, which its call of `place_fields` uses) are `//@ignore-on-host` groundwork and not counted: the root trusts the place body, whose parts 41 and 38 get no answer.
The twins are `//@ignore-on-host` diagnostics run on demand; one runs with
`THRUST_UI_CASE_STUDY=1 COAR_IMAGE=<image> cargo test --test ui -- --ignored univariant_biased_reach_<name>`
(`THRUST_PCSAT_CPUS` sets the CPUs per solver container, `THRUST_UI_THREADS` how many twins run at once).
Their `--cfg` value is single-quoted in the `//@compile-flags` header (`--cfg 'thrust_univariant_biased_reach="<name>"'`),
because the harness splits the header like a shell and drops unquoted double quotes.

| file | selection | state |
| --- | --- | --- |
| `index.rs` | `crate`: the clients `filled`, `two_members` and `column_bound` of `Idx`, `IndexVec`, `IndexSlice`, the bit sets and the own iterators `IdxRange`, `WordIter`, `IterEnumerated`, whose bodies the `rustc_index_*_helpers.rs` roots check, and `IndexVec` and `IndexSlice::index`, analyzed for the function pointer and the read the clients use | verified, each goal on its own |
| `indexvec_int_range.rs` | `rustc_index::vec`, the functions of `rustc_index::slice` but `IterEnumerated::yields_last` (assumed on its contract, which `rustc_index_*_helpers.rs` check; under this option its goal gets no answer), `filled`, under `THRUST_INT_RANGE=conversions` | verified, each class of clauses on its own (`THRUST_SPLIT`); a check of the option, not a run of the case study: with it `count_ones` of bit_set.rs has no specification of `sum` |
| `simple.rs` | `crate`: `drive`, which reads `LayoutData::scalar_pair`'s fields as `univariant_biased` does; `scalar_pair` assumed on its contract, which the generated `univariant_biased_rustc_abi_layout_simple_helpers.rs` root checks | verified |
| `scalar_pair.rs` | `LayoutData::scalar_pair` (layout/simple.rs), with std's `Iterator::max_by_key` on std.rs's contract; `Niche::from_scalar` and `Scalar::size` assumed on their contracts, which `rustc_abi_helpers.rs` checks | verified, each goal on its own (`THRUST_SPLIT_GOALS`); the fail twin asserts, before the niches are computed, that the second scalar is placed at 0, and false after a call of `max_by_key` on a chain of two concrete options (`drive_max_by_key`), which shows the code after such a call reachable under its contract for `u32` items; that it is reachable for `scalar_pair`'s `Niche` items is inferred from this, not run |
| `univariant_caller.rs` | `LayoutCalculator::univariant`, `univariant_biased` trusted on its contract | verified, one part per goal (`THRUST_SPLIT_GOALS`), with the predicates its contracts pass on unchanged `#[thrust::opaque]`: `layout_pre`, which `univariant`'s body reveals, `fits_in_any_order`, `weighs`, `unsized_misplaced`, `some_field_niche` (layout.rs), `Primitive::size_in`, `FieldsShape::arbitrary_of`, `TargetDataLayout::pointer_space_ok`, `TargetDataLayout::pointer_size_is` (lib.rs); `univariant_biased`, `Primitive::size`, `layout()`, `pointer_size_in` and `pointer_align_in` reveal those they read (#132) |
| `weights.rs` | `thrust/weights.rs`: the weighted counting lemmas, ending in `weight_at_le_distinct` (the entries of a non-negative weight sequence at the distinct indices of a selection below `n` sum to at most the first `n` entries), the bound that `BitIter`'s `produces` (its yielded indices are pairwise distinct) feeds | not reached from `layout()`, so no generated root selects it; draft until its run is recorded; its fail twin is `weight_at_le` without its bound on how often an index occurs (`--cfg thrust_weights_fail`) |
| `lemmas.rs` | `split`, the caller of the permutation split of `thrust/lemmas.rs` that `layout()` uses; the counting lemmas' own proofs (the split and its upper bound `permutation_split_le`, the pigeonhole principle `every_index_occurs` that `univariant_biased` uses) are checked by `layout_case_study_lemmas_helpers.rs` | verified |

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
