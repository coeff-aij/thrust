# Loops of Creusot's iterator examples

The loops of Creusot's `examples/iterators/` (creusot-rs/creusot 3620de437) that are clients of an
iterator, with Creusot's code and Thrust's annotations. Each loop has three files: `pass/<name>.rs`
with the written invariant, `fail/<name>.rs` with one wrong claim, and `noinv/<name>.rs`, the pass
file with every `invariant!` removed, left to inference (no `THRUST_FOR_LOOP_HISTORY`). The ui
harness does not read `drafts/`; a file without `main` is compiled with `--crate-type=lib`, as the
harness does.

Changes common to the `for` loops: an element type parameter gets the bound `T: Model`, and each
invariant also states where `iter_old` starts (the argument of the loop's `into_iter`), which
Creusot keeps from the loop's desugaring and Thrust's written invariant, being the whole invariant,
must state. The hand-written `loop` forms keep Creusot's `iter_old` and `produced` snapshots as
`ghost!` values, and their file also holds the iterator they run over, as Creusot's does; that
iterator's impl is the one of `tests/ui/pass/creusot/range.rs` or `iter_mut.rs`, with the shared
`tests/ui/pass/creusot/auxiliary/common.rs`.

| loop | source (3620de437) | class | changed for Thrust | fail twin |
| --- | --- | --- | --- | --- |
| `slice_iter` | `03_std_iterators.rs` line 4 | generic in the element type only (std's `slice::Iter<T>`) | common changes | `result == slice.len() + 1` |
| `vec_iter` | `03_std_iterators.rs` line 15 | generic in the element type only (`&Vec<T>` into std's `slice::Iter<T>`) | common changes | `result == vec.len() + 1` |
| `sum_range` | `03_std_iterators.rs` line 58 | concrete (std's `Range<isize>`) | common changes | `result == n + 1` |
| `enumerate_range` | `03_std_iterators.rs` line 69 | concrete (std's `Enumerate<Range<usize>>`) | common changes, and `requires(true)`/`ensures(true)`; the range is `usize`, which Creusot infers from the invariant comparing index and item, and Thrust from the type of the invariant's `iter`. The function has no postcondition, so the invariant is its only claim and `noinv/enumerate_range.rs` claims nothing | invariant `ix == x + 1` |
| `sum_range_loop` | `01_range.rs` line 65 (`Range` at line 7) | concrete (Creusot's own `Range`) | `snapshot!` as `ghost!`; the invariant also states `iter_old`'s bounds | `result == n + 1` |
| `all_zero_loop` | `02_iter_mut.rs` line 71 (`IterMut` at line 7) | concrete (Creusot's own `IterMut` over `usize`) | `snapshot!` as `ghost!`; the invariant also states that `iter_old` is the borrow of `v` and `IterMut`'s type invariant of `iter_old` and `it`, which Creusot carries implicitly | final elements `== 1` |

Left out: `my_reverse` (`03_std_iterators.rs` line 90, generic in the element type only, over
`Zip<Range<usize>, Range<usize>>`). std.rs specifies `Zip` and the free function `std::iter::zip`,
but neither the method `Iterator::zip` nor `<[T]>::swap`, which the loop calls.

Files: `pass/`, `fail/` and `noinv/` each hold `slice_iter.rs`, `vec_iter.rs`, `sum_range.rs`,
`enumerate_range.rs`, `sum_range_loop.rs` and `all_zero_loop.rs`.
