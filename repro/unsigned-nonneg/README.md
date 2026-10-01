# Unsigned facts: as refinements and as a type

## Status

Two versions of "a value of an unsigned type is non-negative" are on this fork, for a discussion of
where the fact should live. Neither is a patch proposal.

- `uint-models` (`44b72fc6`, this fork's `main`): the fact as a refinement. It carries
  coord-e/thrust#268 (`46c0d0d4`) and #286 (`4b7ee25d`), both unmerged upstream, and extends #268's
  fact to nested positions (`7976671f`, `2df4ee54`). The fact then reaches every position, but the
  emitted queries grow by several times, almost all of it from obligations that hold as written.
- `uint-sort` (`dff36230`, two commits on `44b72fc6`, not in `main`): the fact as part of the type.
  The queries are smaller than before #268 and #286, and the ui suite gives the same verdicts as
  `main`.

Overflow is out of scope for both: the upper bound is not stated, and arithmetic without overflow
checks stays on unbounded integers.

## Refinement version (`uint-models`)

| part | source |
| --- | --- |
| `usize`, `u32` and `u64` model as `model::UInt`; a `UInt` value is refined with `v >= 0`, assumed where read and an obligation where produced, and conjoined to each template in `build_refined` | #268 |
| the fact at a value's root: parameter, return value, local, enum variant field | #268 |
| tuple-element refinements normalized in subtyping; pointee refinements kept through borrows, assignments, calls, branches and loops | #286 |
| the fact on tuple elements, struct fields and the content of `&T` and `&mut T` (`TypeBuilder::field_type`, `PointerType::*_to_refined`) | fork, `7976671f` |
| the fact as an invariant of a `&mut` content, and of the box of a local that the body borrows mutably (`is_mut_borrowed`, `mut_local_content` in `src/analyze/basic_block.rs`) | fork, `7976671f` |
| the fact on the content of the `Mut` model; soundness tests `tests/ui/fail/unsigned_soundness_*` (12) | fork, `2df4ee54` |

`relate_refined_type` (`src/rty/subtyping.rs`) makes the expected refinement the head, and
`ClauseBuilder::head` makes one clause per head atom, each with a copy of the whole body. A
refinement in a nested position travels with the value (#286), so every subtyping on a value with
k unsigned positions gives k clauses. In most of them the value on the left comes with the same
fact, so the clause holds as written. A typical clause, from stage 5:

```
(=> (and (>= (tuple_proj.2 v0) 0) ... (>= (tuple_proj.2 v11) 0) ... true)
    (>= (tuple_proj.2 v11) 0))
```

In stage 5, 107 of the 1470 clauses with head `t >= 0` are about a root variable, the positions
#268 reaches. The other 1363 are about a projection: a field, a tuple element, or the current or
final value of a reference. These are the positions the extension adds.

## Type version (`uint-sort`)

This follows #268's own note that the complete fix needs unsignedness in `rty::Type`.

- `model::UInt` becomes `rty::Type::UInt` (sort `Int`). `TypeBuilder` leaves values unrefined, and
  `RefinedType::formula` adds `v >= 0` for a `UInt` position, including nested ones. The fact is
  therefore assumed wherever a value is in the environment, on the body side only, and is never a
  subtyping obligation.
- The fact is proved only where an unsigned value can come from an unbounded integer:
  - an unsigned `-` without overflow checks gets rustc's overflow assertion on its lower bound
    (`assert_no_underflow`);
  - a ghost term of type `UInt` is required non-negative where it is introduced.

  Every other way of producing an unsigned value stays in range: constants, `+ * / %` on
  non-negative operands, casts (which wrap), and checked arithmetic. Flux treats unsigned values the
  same way: `uint_invariants` gives unsigned types a non-negativity invariant, and with overflow
  checking off, unsigned subtraction carries `requires a - b >= 0` (`ConstrReason::Underflow`).
- `is_mut_borrowed`, `mut_local_content` and the facts conjoined to templates are removed.

Soundness tests: the 12 `unsigned_soundness_*` of `uint-models`, and `unsigned_soundness_ghost`
added on `uint-sort`. The ghost test is not refuted on `uint-models`: there, a ghost term `x - 1`
at `x == 0` contradicts the assumed fact and verifies what follows.

The ui suite on `uint-sort` with 12 tests in parallel: 873 passed, 8 failed, 4 ignored.

- Six of the failures also fail on `main`: `traits/fold`, `fold_fn`, `map_fn`, `map_no_closure`,
  `simple_loop_self_mut_noinv` and `skip_step`.
- The other two, `slice_split_first_loop` and `traits/map_over_filter_item`, time out under that
  load and pass when run alone. On `main`, run alone, `slice_split_first_loop` fails.

## Query sizes

Frontend only, with a stub solver that prints `sat`. Each test file is run with its own
`//@compile-flags` and `//@rustc-env`, from the root of a worktree after `cargo build --workspace`:

```sh
LD_LIBRARY_PATH=$(rustc --print sysroot)/lib THRUST_OUTPUT_DIR=<dir> THRUST_SOLVER=<stub> \
  THRUST_TRY_SPECS=1 target/debug/thrust-rustc --edition 2024 -Adead_code -C debug-assertions=off \
  -o <dir>/a.out tests/ui/pass/rustc_coroutine/univariant.rs
```

`f05d3dd2` is `main` before #268 and #286 were merged. The `uint-sort` column was taken at
`4a77d0de`, its first commit.

| query | `f05d3dd2` | `uint-models` `44b72fc6` | `uint-sort` |
| --- | --- | --- | --- |
| stage 3 `bitset.rs` | | 430 clauses, 1.8 MB | 112 clauses, 0.3 MB |
| stage 5 `eligibility.rs` | 732 clauses, 6.7 MB | 2150 clauses, 35 MB | 666 clauses, 6.4 MB |
| stage 6 `univariant.rs` | 1785 clauses, 20.5 MB | 11273 clauses, 743 MB | 1535 clauses, 17 MB |

## Solver

CoAR built from fptprove `develop` `96d99c747`, `pcsat_tbq_ar.json`, `-p pcsp`, 2 CPUs, 6 GB,
60 s cap. "Valid removed" is `uint-models` with the clauses whose head is a body conjunct removed.

| query | `uint-models` | valid removed | `uint-sort` |
| --- | --- | --- | --- |
| `bitset`, pass | `sat` 1.6 s, 1.7 s | `sat` 13.6 s | |
| `bitset`, fail | `unsat` 6.8 s, 17.9 s | `unsat` 27.1 s | |
| `eligibility` | killed at 6 GB, 54.7 s and 55.0 s | killed at 6 GB, 44.2 s | no answer at 60 s (1 run) |
| `univariant`, pass | no answer at 60 s | not run | `sat` 49.1 s (1 run) |

Neither side of `bitset` was timed on `uint-sort`. Both sides pass in the ui suite on the image
the test pins. The fail side of `univariant` has not been run on `uint-sort`.

## Question

Is the type form the direction #268 should take? In particular: assuming the fact in
`RefinedType::formula` for every `UInt` position, and proving it only at the two places above.
