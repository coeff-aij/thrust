# Creusot benchmark cases

Cases from the Creusot artifact's iterator benchmark, each verified with a specification
equivalent to Creusot's, plus nine additions with no Creusot counterpart (`take_count.rs`,
`fold.rs`, `try_fold.rs`, `find.rs`, `filter.rs`, and the forms of the last four generic in the
iterator and the closure, in `generic/`). `<file>.rs` is the pass side;
`tests/ui/fail/creusot/<file>.rs` is its fail twin (two extra fail-only files:
`collect_for_contract.rs` and `extend_for_contract.rs` break the postcondition of `collect` and
`extend` themselves, where the twins of `collect_for.rs` and `extend_for.rs` break the client's
assertion). `weaker/` holds
variants of a case whose property is weaker than Creusot's but still verifies.

`range.rs`, `take.rs`, `skip.rs`, `fuse_produces.rs`, `map.rs`, `map_ext.rs` and `iter_mut.rs` are
Creusot's code (3620de437) with only the rewrites Thrust needs (`skip.rs`'s `next` has the control
flow of the 2022 artifact and moves `self` into a local, so that its written loop invariant can name
`self`'s value at entry through a `FnParam` binder named `self`), without `main`, and share one file,
`auxiliary/common.rs`, through `#[path = "auxiliary/common.rs"] mod common;`, as Creusot's cases
share `common.rs` (the ui harness does not run files under `auxiliary/`). As in Creusot's
`common.rs`, its `produces_refl` has no premise, where the trait block the other files repeat
requires the impl's `invariant`. Every other file in the
`produces` form repeats one trait block, Creusot's `common.rs` in Thrust syntax:
the predicates, the laws `produces_refl` and `produces_trans` in concatenation form (the latter
without Creusot's invariant premises, which a Thrust loop head cannot supply for its entry state),
`invariant` defaulting to `true`, and `next` with Creusot's contract. Each law has a default empty
body in the trait, and Thrust checks it at every impl that does not write it, where Creusot restates
it in each impl with an empty body; no impl writes a proof of its own, and no case calls a lemma,
except `counter_creusot_lemma.rs`, whose `Map` impl proves `produces_trans` by lemmas
(`fuse_produces_result.rs` declares its trait's laws without a default and restates them per impl
with empty bodies, as Creusot does). The step-form files repeat theirs in the same layout. A case that needs `collect` adds it to its copy after `next`.

| file | Creusot benchmark file | form |
| --- | --- | --- |
| `range.rs` | `examples/iterators/01_range.rs` (3620de437) | `produces` |
| `take.rs` | `examples/iterators/16_take.rs` (3620de437) | `produces` |
| `skip.rs` | `examples/iterators/04_skip.rs` (3620de437), `next` in the control flow of the 2022 artifact's `iterators/skip.rs` | `produces`, concatenated |
| `fuse.rs` | `iterators/fuse.rs` | `step` |
| `fuse_produces.rs` | the current Creusot's `examples/iterators/07_fuse.rs` (3620de437) | `produces` + `FusedIterator::is_fused` with its state `Option<I>` and its `completed` and `produces` |
| `fuse_produces_result.rs` | `iterators/fuse.rs` | `produces` + `FusedIterator::is_fused` with Creusot's state `Result<I, Ghost<I>>`; `next` keeps `iter` live past the ghost of the exhausted iterator, as Creusot's `ghost! { *iter }` reads it |
| `map.rs` | `examples/iterators/05_map.rs` (3620de437) | `produces` over an `FnMut` closure with the chain `fs` of closure states and `hist_inv!`, both laws inherited with no lemma, fully checked |
| `iter_mut.rs` | the current Creusot's `examples/iterators/02_iter_mut.rs` (3620de437) | `produces` over Creusot's `IterMut { inner: &mut [T] }`, whose `next` (`split_off_first_mut`) is checked, Creusot's constructor `iter_mut(v)` (`IterMut { inner: &mut v[..] }`, with its type invariant, which needs std.rs's length-keeping `IndexMut`); 02's `all_zero` client over this `IterMut` is not ported, and `all_zero.rs` states its property over std's `slice::IterMut` |
| `collect.rs` | `common.rs` (`collect` / `FromIterator`) | `produces` |
| `all_zero.rs` | `examples/all_zero.rs` | a `for` loop over std's `slice::IterMut` with its `next` through std.rs, the invariant over the loop's `iter` (`slice::IterMut` has no `IteratorSpec`, so no `produced`; Creusot's own `IterMut` and constructor are in `iter_mut.rs`) |
| `decuple_range.rs` | `examples/decuple_range.rs` | `produces`, positional property, fully checked |
| `skip_take.rs` | `skip_take` of `examples/iterators/03_std_iterators.rs` (3620de437) | Creusot's client over std's `take` and `skip` through std.rs's `IteratorSpec`, generic in `I`, with Creusot's `proof_assert!` |
| `counter.rs` | `examples/counter.rs` | `step` + a unary `next_item` guard, `MapInv`'s ghost history |
| `counter_creusot.rs` | the current Creusot's `counter` in `examples/iterators/03_std_iterators.rs` (3620de437) | `produces` with Creusot's property over `v.iter()` of a `Vec<u32>` (`x == v`, `cnt == x.len()`), the closure's postconditions (the step and the history fact) written where Creusot takes its contract from the body, its precondition inferred, std's `slice::Iter` through its std.rs model, `MapInv` over an `FnMut` closure whose states are related by `hist_inv!` (Creusot's `hist_inv`), as in creusot-std's `std/iter/map_inv.rs` |
| `counter_creusot_lemma.rs` | `examples/counter.rs` | `counter_creusot.rs` with the witnesses of `produces_trans` written as source-level lemmas (Creusot's session gives them by hand) |
| `map_ext.rs` | `examples/iterators/06_map_precond.rs` (3620de437) | `produces` with an existential input sequence, `MapInv`'s ghost history, over an `FnMut` closure with the chain `fs` and `hist_inv!` as `counter_creusot.rs` |
| `extend.rs` | `examples/extend.rs` of the 2022 artifact | `produces` with a local `Extend` trait; a debugging example, the benchmark's forms are `concat_vec.rs` and `extend_for.rs` |
| `collect_for.rs` | the current Creusot's `examples/iterators/08_collect_extend.rs` (3620de437), `collect` and `collect_example` | std.rs's `IteratorSpec`, a `for` loop whose invariant states the vector is `produced` |
| `concat_vec.rs` | `examples/extend.rs` of the 2022 artifact, `extend_index` | std's `Vec::extend` over `v2.into_iter()` under std.rs's contract of `Vec::extend` (Creusot's) |
| `extend_for.rs` | the current Creusot's `examples/iterators/08_collect_extend.rs` (3620de437), `extend` and `extend_index` | std.rs's `IteratorSpec`, a `for` loop whose invariant states the vector is its entry value followed by `produced` |
| `take_count.rs` | no counterpart | `produces`; an extra call site of `take.rs`'s `Take` |
| `fold.rs` | no counterpart | `produces`; a hand-written `fold` with a closure contract over the accumulator |
| `try_fold.rs` | no counterpart | `produces`; a hand-written `try_fold` that returns `None` on an early bound crossing |
| `find.rs` | no counterpart | `produces`; linear search over a `Range` |
| `filter.rs` | no counterpart | `produces`; collects a `Range`'s items above a bound |

Generic forms (`generic/`): `fold`, `try_fold`, `find` and `filter` generic in the iterator and an
`FnMut` closure, called at `Range`, each closure's contract stated for every closure state. `<name>.rs`
writes the loop invariant; `<name>_noinv.rs` is the same with every `invariant!` removed, left to
inference. Every `_noinv` pair but `filter_noinv.rs` verifies from fptprove `082cd295c` on;
`filter_noinv.rs`, whose loop has to carry the ghost chain of the `produces` form, gets no answer
within 300 s at fptprove `b9f9c9c05` and is ignored on the host.

| file | what |
| --- | --- |
| `fold.rs`, `fold_noinv.rs` | `fold` generic in `I: Iterator` and `F: FnMut` |
| `try_fold.rs`, `try_fold_noinv.rs` | `try_fold` generic in `I` and `F: FnMut` with `Option` as the `Try` type |
| `find.rs`, `find_noinv.rs` | `find` generic in `I` and a `P: FnMut` predicate taking the item by value |
| `filter.rs`, `filter_noinv.rs` | `filter` into a `Vec`, generic in `I` and `P: FnMut`, in the `produces` form: `iter` produced `s` and completed, and the result is the items of `s` the predicate's calls along `s` accepted, in order (Creusot's `Filter::produces`, with its index map) |

`generic/std/find.rs` writes `find` as std does: a call of `try_fold` with a closure `check` that
breaks with the first item the predicate accepts, so `try_fold` holds the only loop. As in std,
`check` takes `try_fold`'s accumulator `()`, the predicate takes `&I::Item`, and the result is
`break_value()`; the file header lists what still differs. `find` states std.rs's specification of
`Iterator::find` with the accepting state reachable from the first: on `None`, `iter` produced some
items and completed; on `Some(v)`, it produced some items and then `v`, which the predicate
accepted in a state reachable from its first (that it rejected the items before `v` is not
stated). `try_fold` states the same of a `Break`. Both
specifications relate closure states by `hist_inv!`, and `check`, which owns the predicate, states
its own relation through the predicate's in a `hist_inv` clause; it verifies from fptprove
`7d11252b2` on; its fail twin weakens `find`'s `ensures` to a predicate result of `false`.
`generic/std/find_noinv.rs` drops `try_fold`'s loop invariant. `generic/std/find_pre.rs` is the same without `find`'s `ensures`;
its fail twin drops `find`'s precondition on the predicate.

`generic/std/fold_map.rs`, `fold_mapinv.rs`, `try_fold_map.rs` and `try_fold_mapinv.rs` are std's
`Iterator::fold` and `Iterator::try_fold` with std's bodies (`try_fold` with `?`, the `Try` type
fixed to `Option<B>`, needing `THRUST_TRY_SPECS=1`), specified in the forms of Creusot's `Map`
(`map.rs`) and `MapInv` (`map_ext.rs`, the closure also receiving the ghost history of the items
before the current one): the closure states and accumulators along the produced items form a chain
of call postconditions, held in ghost variables across the loop, and the closure may be called at
every state the chain reaches. Each client derives its bound from the chain. The fail twins of
`fold_map.rs`, `fold_mapinv.rs`, `try_fold_map.rs` and `try_fold_mapinv.rs` assert a bound the
result does not reach (the running maximum over `0..10` is 9). The pass side of `try_fold_mapinv.rs` is ignored while the solver gives no
answer at 300 s.

`generic/std/advance_by.rs`, `advance_by_ghost.rs` and `extend_desugared.rs` are std's loops over
std.rs's `IteratorSpec`, specified with Creusot's `produces` and `completed`; each file's header
gives the std function and what differs. `advance_by.rs` is the default `Iterator::advance_by`
(`spec_advance_by`, core) with std's body; `advance_by_ghost.rs` writes the `is_none` test as a
`match` and records the dropped items in a ghost sequence; `extend_desugared.rs` is
`Vec::extend_desugared` (alloc) with `push` for the capacity handling and a ghost sequence of the
items taken, its parameters moved into locals for the same reason as in `skip.rs`. std runs the `advance_by` loop only for unsized iterators; a `Sized` iterator takes a
`try_fold` specialisation, so these two verify the fallback loop. `advance_by_ghost.rs` is kept to
compare an explicit ghost witness with the existential the invariant of `advance_by.rs` infers. The
fail twins return an error one too small (`advance_by*`) or discard each item (`extend_desugared`).

Weaker variants (`weaker/`, still verify):

| file | weaker than | how |
| --- | --- | --- |
| `map.rs` | `map.rs` | `step` + a unary `next_item` guard instead of the ternary `produces` |
| `map_call.rs` | `map.rs` | the same, at a call site with a partial closure |
| `collect_mutref.rs` | `collect.rs` | `collect(&mut self)` / `from_iter(&mut I)` instead of by value |
| `decuple_range.rs` | `decuple_range.rs` | the `step` form's positionless property (every element in range) instead of `v[i] == 10 * i` |

Every case's probe programs are drafts,
not yet verified or superseded by the files above: see [drafts/creusot/README.md](../../../../drafts/creusot/README.md).
