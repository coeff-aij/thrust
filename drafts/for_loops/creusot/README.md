# `for`-loop cases of Creusot's `hillel` and `knights_tour`

Creusot's executable code (creusot-rs/creusot 3620de437) with Thrust's annotations, one pass file
per source function group and a fail twin that breaks a functional property. The ui harness does
not read `drafts/`; each file is compiled with `--crate-type=lib`.

| file | source (3620de437) | what it ports |
| --- | --- | --- |
| `pass/hillel.rs` | `examples/hillel.rs` | `insert_unique` (`for` over `vec.iter()`) and `unique` (`for` over `0..str.len()`), generic in the element type |
| `pass/hillel_pad.rs` | `examples/hillel.rs` | `right_pad` and `left_pad` (`while` loops over `Vec::push` and `Vec::insert`) |
| `pass/hillel_fulcrum.rs` | `examples/hillel.rs` | `fulcrum` (two `for` loops) with `sum_range`, `score`, `sum_range_split` and the lemmas that restate Creusot's automatic steps |
| `pass/hillel_fulcrum_is_min.rs` | `examples/hillel.rs` | `hillel_fulcrum.rs` with the postcondition's `forall` stated through its recursive form `is_min` |
| `pass/knights_tour.rs` | `tests/should_succeed/vector/06_knights_tour.rs` | `Point::mov`, `Board::{new, available, count_degree, set}`, `moves` (trusted, as in Creusot), `min` and `knights_tour` |
| `fail/hillel.rs`, `fail/hillel_insert_unique.rs` | | `unique` claims `result.len() == str.len()`; `insert_unique` claims the element is always appended |
| `fail/hillel_right_pad.rs`, `fail/hillel_left_pad.rs`, `fail/hillel_fulcrum.rs` | | the pads claim the result always has length `len`; `fulcrum` also claims index 0 |
| `fail/knights_tour_mov.rs`, `fail/knights_tour_min.rs`, `fail/knights_tour_new.rs` | | `mov` claims `result.x == self.x + p.0 + 1`; `min` claims `result == None`; `new` claims `result.size == size + 1` |

Changes for Thrust, besides the annotations:

- `T: DeepModel` is `T: Model + ModelEq`, so `deep_model()` is the model itself.
- Creusot's `Snapshot`s that only feed `proof_assert!` are dropped; `proof_assert!` and the lemma
  calls that the solver needs stay (`unique`'s two are not needed).
- `insert_unique` rebinds `vec` as `v` (`let v = vec;`), so that the invariant can name both the
  loop-carried reference and the parameter's entry value, as `tests/ui/pass/ghost_seq_loop.rs`.
- Each invariant also states `iter_old` (where the iterator starts) and every fact about an
  unchanged variable that the loop must keep (`is_unique(*v)`, `wf`, `in_bounds`), which Creusot
  carries implicitly.
- `Board::new` builds its rows in a `for` loop where Creusot calls `map_inv(..).collect()`.
- `Point` and `Board` get `impl Model` as their own model and `derive(PartialEq)` for it; `knights_tour`
  has no `dumb_nonlinear_arith`, since overflow is not checked with `debug-assertions=off`.
- `fulcrum`'s `sum_range`, `score` and lemmas are over `usize` arguments and an `i64` result (a
  `u32` result is checked to be non-negative by induction, which the elements' model does not
  support); `elem_nonneg` is a trusted lemma that an element of a `u32` slice is not negative: Thrust
  does not assume it of a value read in a specification (a slice element, a struct's `u32` field, a
  `usize` bound by `forall`), where Creusot's `u32@` is in range. `wf` writes `0 <= i` for the same
  reason. The loops' steps call
  `sum_range_snoc`, `sum_range_split` and `sum_range_nonneg`; the first loop has a counter `k`
  (`let mut k: usize = 0`), since a ghost value cannot be passed to a lemma as a `usize`.
- The `while` loops of `right_pad` and `left_pad` rebind `str` as `s`, keep `old_str` and `c` as
  `ghost!` values, and restate in the invariant the facts about the loop's variables.

std.rs specifications added with this change: `abs_diff` for the signed and unsigned integer types
(`tests/ui/{pass,fail}/uint_abs_diff.rs`) and `Vec::insert` (`tests/ui/{pass,fail}/vec_insert.rs`,
`tests/ui/fail/vec_insert_pre.rs` for the index precondition). `map_inv` has no std.rs specification,
so `Board::new` keeps its `for` form.

## Results

fptprove build 358438811, `pcsat_thrust.json`, 2 CPUs and 8 GB, 120 s limit, one run each, seconds of
wall time of the whole `thrust-rustc` call, so provisional upper bounds. The per-function
`knights_tour.rs` runs use `THRUST_VERIFY_ONLY`, which assumes the other functions' contracts.

| case | result |
| --- | --- |
| `hillel.rs` (`insert_unique` + `unique`) | `sat`, 8.7 s; twins `unsat`, 10.6 s and 24.0 s |
| `hillel_pad.rs` (`right_pad`, `left_pad`) | `sat`, 2.2 s; twins `unsat`, 2.2 s and 2.3 s |
| `hillel_fulcrum_is_min.rs` | `sat`, 9.2 s; twin `unsat`, 10.8 s |
| `hillel_fulcrum.rs` | timeout (100 s): `min_all`, the step from `is_min` to the postcondition's `forall` |
| `knights_tour.rs`, `Point::mov` | `sat`, 1.4 s; twin `unsat`, 1.4 s |
| `knights_tour.rs`, `Board::count_degree` | `sat`, 3.3 s |
| `knights_tour.rs`, `min` | `sat`, 11.7 s; twin `unsat`, 17.9 s |
| `knights_tour.rs`, `knights_tour` (others assumed) | `sat`, 6.3 s |
| `knights_tour.rs`, `Board::available` | `unknown`, 38.8 s: the step from `(p.x as usize) < self.size` to `p.x < self.size` (the cast of an `isize`); without `ensures(result ==> in_bounds(..))` `sat` in 2 s |
| `knights_tour.rs`, `Board::set` | `sat`, 2.2 s |
| `knights_tour.rs`, `Board::new` | `sat`, 2.5 s; twin `unsat`, 5.6 s |

`hillel_fulcrum.rs` verifies everything but that last step: with the postcondition through `is_min`
it is `sat`. The whole of `knights_tour.rs` is a timeout at 115 s because of `Board::available`.
