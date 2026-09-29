# Creusot benchmark cases

Fourteen cases from the Creusot artifact's iterator benchmark, each verified with a specification
equivalent to Creusot's, plus five additions with no Creusot counterpart (`take_count.rs`,
`fold.rs`, `try_fold.rs`, `find.rs`, `filter.rs`). `<file>.rs` is the pass side;
`tests/ui/fail/creusot/<file>.rs` is its fail twin (one extra fail-only file,
`skip_take_take_count.rs`, twins `skip_take.rs` on a different property). `weaker/` holds
variants of a case whose property is weaker than Creusot's but still verifies.

Every file in the `produces` form repeats one trait block, Creusot's `common.rs` in Thrust syntax:
the predicates, the laws `produces_refl` and `produces_trans` in concatenation form (the latter
without Creusot's invariant premises, which a Thrust loop head cannot supply for its entry state),
`invariant` defaulting to `true`, and `next` with Creusot's contract. The step-form files repeat
theirs in the same layout. A case that needs `collect` adds it to its copy after `next`.

| file | Creusot benchmark file | form |
| --- | --- | --- |
| `range.rs` | `iterators/range.rs` | `produces` |
| `take.rs` | `iterators/take.rs` | `produces` |
| `skip.rs` | `iterators/skip.rs` | `produces`, concatenated |
| `fuse.rs` | `iterators/fuse.rs` | `step` |
| `fuse_produces.rs` | `iterators/fuse.rs` | `produces` + `FusedIterator::is_fused`; state `Option<I>` for Creusot's `Result<I, Ghost<I>>` |
| `map.rs` | `iterators/map.rs` | `produces`, Creusot's own proof structure (source-level lemmas), fully checked |
| `iter_mut.rs` | `iterators/iter_mut.rs` | `produces` |
| `collect.rs` | `common.rs` (`collect` / `FromIterator`) | `produces` |
| `all_zero.rs` | `examples/all_zero.rs` | `produces`, via `iter_mut` |
| `decuple_range.rs` | `examples/decuple_range.rs` | `produces`, positional property, fully checked |
| `skip_take.rs` | `examples/skip_take.rs` | `produces`, concatenated `Skip`, generic in `I` |
| `counter.rs` | `examples/counter.rs` | `step` + a unary `next_item` guard, `MapInv`'s ghost history |
| `map_ext.rs` | `iterators/map_ext.rs` | `produces` with an existential input sequence, `MapInv`'s ghost history (the ninth adapter) |
| `extend.rs` | `examples/extend.rs` | `produces` |
| `take_count.rs` | no counterpart | `produces`; an extra call site of `take.rs`'s `Take` |
| `fold.rs` | no counterpart | `produces`; a hand-written `fold` with a closure contract over the accumulator |
| `try_fold.rs` | no counterpart | `produces`; a hand-written `try_fold` that returns `None` on an early bound crossing |
| `find.rs` | no counterpart | `produces`; linear search over a `Range` |
| `filter.rs` | no counterpart | `produces`; collects a `Range`'s items above a bound |

Weaker variants (`weaker/`, still verify):

| file | weaker than | how |
| --- | --- | --- |
| `map.rs` | `map.rs` | `step` + a unary `next_item` guard instead of the ternary `produces` |
| `map_call.rs` | `map.rs` | the same, at a call site with a partial closure |
| `collect_mutref.rs` | `collect.rs` | `collect(&mut self)` / `from_iter(&mut I)` instead of by value |
| `decuple_range.rs` | `decuple_range.rs` | the `step` form's positionless property (every element in range) instead of `v[i] == 10 * i` |

`fuse_produces_result.rs` (Fuse with
Creusot's `Result<I, Ghost<I>>` state) and every case's probe programs are drafts,
not yet verified or superseded by the files above: see [drafts/creusot/README.md](../../../../drafts/creusot/README.md).
