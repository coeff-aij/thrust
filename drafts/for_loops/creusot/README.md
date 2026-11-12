# `for`-loop cases of Creusot's `hillel` and `knights_tour`

Creusot's executable code (creusot-rs/creusot 3620de437) with Thrust's annotations, one pass file
per source function group and a fail twin that breaks a functional property. The ui harness does
not read `drafts/`; each file is compiled with `--crate-type=lib`.

| file | source (3620de437) | what it ports |
| --- | --- | --- |
| `pass/hillel.rs` | `examples/hillel.rs` | `insert_unique` (`for` over `vec.iter()`) and `unique` (`for` over `0..str.len()`), generic in the element type |
| `pass/hillel_fulcrum.rs` | `examples/hillel.rs` | `fulcrum` (two `for` loops) with `sum_range`, `score` and `sum_range_split`; stops at `u32::abs_diff` |
| `pass/hillel_fulcrum_abs_diff.rs` | `examples/hillel.rs` | `hillel_fulcrum.rs` with `abs_diff` behind a trusted local function carrying the contract of std.rs's `i32::abs_diff` |
| `pass/knights_tour.rs` | `tests/should_succeed/vector/06_knights_tour.rs` | `Point::mov`, `Board::{new, available, count_degree, set}`, `moves` (trusted, as in Creusot), `min` and `knights_tour` |
| `fail/hillel.rs`, `fail/hillel_insert_unique.rs` | | `unique` claims `result.len() == str.len()`; `insert_unique` claims the element is always appended |
| `fail/knights_tour_mov.rs`, `fail/knights_tour_min.rs` | | `mov` claims `result.x == self.x + p.0 + 1`; `min` claims `result == None` |

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
- `fulcrum`'s `sum_range`, `score` and the lemmas are over `usize`/`u32` arguments (the logic's
  integers are unbounded, so there is no overflow in them).

Missing std.rs specifications: `u32::abs_diff` (only `i32::abs_diff` has one), which `fulcrum`
calls; none was added.

## Results

fptprove build 358438811 (`coar:latest`), `pcsat_thrust.json`, 2 CPUs and 8 GB, 120 s limit, one run
each, seconds of wall time of the whole `thrust-rustc` call, so provisional upper bounds. The
per-function runs use `THRUST_VERIFY_ONLY`, which assumes the contracts of the other functions.

| case | result |
| --- | --- |
| `hillel.rs` (`insert_unique` + `unique`) | `sat`, 8.7 s |
| `fail/hillel.rs` | `unsat`, 24.0 s |
| `fail/hillel_insert_unique.rs` | `unsat`, 10.6 s |
| `hillel_fulcrum.rs` | error: no specification of `u32::abs_diff` |
| `hillel_fulcrum_abs_diff.rs` | `unsat`, 7.5 s: the first loop's step `total == sum_range(s, 0, produced.len())` needs the induction fact `sum_range(0, k + 1) == sum_range(0, k) + s[k]`, and the loop body names no index to call a lemma at |
| `knights_tour.rs`, `Point::mov` | `sat`, 1.4 s |
| `knights_tour.rs`, `Board::count_degree` | `sat`, 3.3 s |
| `knights_tour.rs`, `min` | `sat`, 11.7 s |
| `knights_tour.rs`, `knights_tour` (others assumed) | `sat`, 6.3 s |
| `knights_tour.rs`, `Board::available` | `unknown`, 26.8 s; without `ensures(result ==> in_bounds(..))` it is `sat` in 2 s |
| `knights_tour.rs`, `Board::set` | `unknown`, 59.1 s; without `ensures(wf(&!self))` it is `sat` in 1 s |
| `knights_tour.rs`, `Board::new` | `unsat`, 2.6 s: the row lengths `forall(i) result.field[i].len() == size` (`result.field.len() == size` alone is `sat`) |
| `fail/knights_tour_mov.rs` (`Point::mov`) | `unsat`, 1.4 s |
| `fail/knights_tour_min.rs` (`min`) | `unsat`, 17.9 s |

The whole of `knights_tour.rs` is not `sat`: `Board::new` is refuted on the row-length part of
`wf`, and `available` and `set` end `unknown`; the client `knights_tour` verifies against their
contracts.
