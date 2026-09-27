# Creusot benchmark cases

Thirteen cases from the Creusot artifact's iterator benchmark, each verified with a specification
equivalent to Creusot's. `<file>.rs` is the pass side; `tests/ui/fail/creusot/<file>.rs` is its
fail twin (one extra fail-only file, `skip_take_take_count.rs`, twins `skip_take.rs` on a
different property). `weaker/` holds variants of a case whose property is weaker than Creusot's but
still verifies.

| file | Creusot benchmark file | form |
| --- | --- | --- |
| `range.rs` | `iterators/range.rs` | `produces` |
| `take.rs` | `iterators/take.rs` | `produces` |
| `skip.rs` | `iterators/skip.rs` | `produces`, concatenated |
| `fuse.rs` | `iterators/fuse.rs` | `step` |
| `map.rs` | `iterators/map.rs` | `produces`, Creusot's own proof structure (source-level lemmas), fully checked |
| `iter_mut.rs` | `iterators/iter_mut.rs` | `produces` |
| `collect.rs` | `common.rs` (`collect` / `FromIterator`) | `produces` |
| `all_zero.rs` | `examples/all_zero.rs` | `produces`, via `iter_mut` |
| `decuple_range.rs` | `examples/decuple_range.rs` | `produces`, positional property, fully checked |
| `skip_take.rs` | `examples/skip_take.rs` | `produces`, concatenated `Skip`, generic in `I` |
| `counter.rs` | `examples/counter.rs` | `step` + a unary `next_item` guard, `MapInv`'s ghost history |
| `extend.rs` | `examples/extend.rs` | `produces` |
| `take_count.rs` | no counterpart | `produces`; an extra call site of `take.rs`'s `Take` |

Weaker variants (`weaker/`, still verify):

| file | weaker than | how |
| --- | --- | --- |
| `map.rs` | `map.rs` | `step` + a unary `next_item` guard instead of the ternary `produces` |
| `map_call.rs` | `map.rs` | the same, at a call site with a partial closure |
| `collect_mutref.rs` | `collect.rs` | `collect(&mut self)` / `from_iter(&mut I)` instead of by value |
| `decuple_range.rs` | `decuple_range.rs` | the `step` form's positionless property (every element in range) instead of `v[i] == 10 * i` |

`map_ext.rs` (Creusot's `MapInv`, the ninth adapter) and every case's probe programs are drafts,
not yet verified or superseded by the files above: see [drafts/creusot/README.md](../../../../drafts/creusot/README.md).
