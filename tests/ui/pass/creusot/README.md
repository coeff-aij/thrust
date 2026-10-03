# Creusot benchmark cases

Fourteen cases from the Creusot artifact's iterator benchmark, each verified with a specification
equivalent to Creusot's, plus nine additions with no Creusot counterpart (`take_count.rs`,
`fold.rs`, `try_fold.rs`, `find.rs`, `filter.rs`, and the forms of the last four generic in the
iterator and the closure, in `generic/`). `<file>.rs` is the pass side;
`tests/ui/fail/creusot/<file>.rs` is its fail twin (one extra fail-only file,
`skip_take_take_count.rs`, twins `skip_take.rs` on a different property). `weaker/` holds
variants of a case whose property is weaker than Creusot's but still verifies.

Every file in the `produces` form repeats one trait block, Creusot's `common.rs` in Thrust syntax:
the predicates, the laws `produces_refl` and `produces_trans` in concatenation form (the latter
without Creusot's invariant premises, which a Thrust loop head cannot supply for its entry state),
`invariant` defaulting to `true`, and `next` with Creusot's contract. Each law has a default empty
body in the trait, and Thrust checks it at every impl that does not write it, where Creusot restates
it in each impl with an empty body; an impl writes a law only when it needs proof steps (the
`produces_trans` of `map`, `map_ext` and `counter_creusot`), or when the solver does not answer the
inherited check (`map`'s `produces_refl`). The step-form files repeat theirs in the
same layout. A case that needs `collect` adds it to its copy after `next`.

| file | Creusot benchmark file | form |
| --- | --- | --- |
| `range.rs` | `iterators/range.rs` | `produces` |
| `take.rs` | `iterators/take.rs` | `produces` |
| `skip.rs` | `iterators/skip.rs` | `produces`, concatenated |
| `fuse.rs` | `iterators/fuse.rs` | `step` |
| `fuse_produces.rs` | the current Creusot's `examples/iterators/07_fuse.rs` (3620de437) | `produces` + `FusedIterator::is_fused` with its state `Option<I>` and its `completed` and `produces` |
| `fuse_produces_result.rs` | `iterators/fuse.rs` | `produces` + `FusedIterator::is_fused` with Creusot's state `Result<I, Ghost<I>>`; `next` keeps `iter` live past the ghost of the exhausted iterator, as Creusot's `ghost! { *iter }` reads it |
| `map.rs` | `iterators/map.rs` | `produces` over an `FnMut` closure with the chain `fs` of closure states and `hist_inv!`, `produces_trans` by one source-level lemma, nothing else needs one, fully checked |
| `iter_mut.rs` | `iterators/iter_mut.rs` | `produces` |
| `collect.rs` | `common.rs` (`collect` / `FromIterator`) | `produces` |
| `all_zero.rs` | `examples/all_zero.rs` | `produces`, via `iter_mut` |
| `decuple_range.rs` | `examples/decuple_range.rs` | `produces`, positional property, fully checked |
| `skip_take.rs` | `examples/skip_take.rs` | `produces`, concatenated `Skip`, generic in `I` |
| `counter.rs` | `examples/counter.rs` | `step` + a unary `next_item` guard, `MapInv`'s ghost history |
| `counter_creusot.rs` | `examples/counter.rs` | `produces` with Creusot's property (`x == v`, `cnt == x.len()`), `MapInv` over an `FnMut` closure whose states are related by `hist_inv!` (Creusot's `hist_inv`), as in creusot-std's `std/iter/map_inv.rs` |
| `map_ext.rs` | `iterators/map_ext.rs` | `produces` with an existential input sequence, `MapInv`'s ghost history, over an `FnMut` closure with the chain `fs` and `hist_inv!` as `counter_creusot.rs` (the ninth adapter) |
| `extend.rs` | `examples/extend.rs` | `produces` |
| `take_count.rs` | no counterpart | `produces`; an extra call site of `take.rs`'s `Take` |
| `fold.rs` | no counterpart | `produces`; a hand-written `fold` with a closure contract over the accumulator |
| `try_fold.rs` | no counterpart | `produces`; a hand-written `try_fold` that returns `None` on an early bound crossing |
| `find.rs` | no counterpart | `produces`; linear search over a `Range` |
| `filter.rs` | no counterpart | `produces`; collects a `Range`'s items above a bound |

Generic forms (`generic/`): `fold`, `try_fold`, `find` and `filter` generic in the iterator and an
`FnMut` closure, called at `Range`, each closure's contract stated for every closure state. `<name>.rs`
writes the loop invariant; `<name>_noinv.rs` is the same with every `invariant!` removed, left to
inference. Every `_noinv` pair verifies from fptprove `082cd295c` on.

| file | what |
| --- | --- |
| `fold.rs`, `fold_noinv.rs` | `fold` generic in `I: Iterator` and `F: FnMut` |
| `try_fold.rs`, `try_fold_noinv.rs` | `try_fold` generic in `I` and `F: FnMut` with `Option` as the `Try` type |
| `find.rs`, `find_noinv.rs` | `find` generic in `I` and a `P: FnMut` predicate taking the item by value |
| `filter.rs`, `filter_noinv.rs` | `filter` into a `Vec`, generic in `I` and `P: FnMut` |

`generic/std/find.rs` writes `find` as std does: a call of `try_fold` with a closure `check` that
breaks with the first item the predicate accepts, so `try_fold` holds the only loop. As in std,
`check` takes `try_fold`'s accumulator `()`, the predicate takes `&I::Item`, and the result is
`break_value()`; the file header lists what still differs. Both
specifications relate closure states by `hist_inv!`, and `check`, which owns the predicate, states
its own relation through the predicate's in a `hist_inv` clause; it verifies from fptprove
`7d11252b2` on. `generic/std/find_pre.rs` is the same without `find`'s `ensures`; its fail twin
drops `find`'s precondition on the predicate.

Weaker variants (`weaker/`, still verify):

| file | weaker than | how |
| --- | --- | --- |
| `map.rs` | `map.rs` | `step` + a unary `next_item` guard instead of the ternary `produces` |
| `map_call.rs` | `map.rs` | the same, at a call site with a partial closure |
| `collect_mutref.rs` | `collect.rs` | `collect(&mut self)` / `from_iter(&mut I)` instead of by value |
| `decuple_range.rs` | `decuple_range.rs` | the `step` form's positionless property (every element in range) instead of `v[i] == 10 * i` |

Every case's probe programs are drafts,
not yet verified or superseded by the files above: see [drafts/creusot/README.md](../../../../drafts/creusot/README.md).
