# Unsigned facts as refinements, and the clauses they give

## Status

This fork's `main` (from `c8799521`) carries coord-e/thrust#268 (`46c0d0d4`) and #286
(`4b7ee25d`), both unmerged upstream, and extends #268's fact to nested positions on the branch
`uint-models` (`7976671f`, `2df4ee54`). This replaces the fork's earlier provisional fix
(`022b28c`, parameters and results only). With the extension the fact reaches every position,
but the emitted queries grow by several times, almost all of it from obligations that hold as
written. This bundle records what was built and measured, for a discussion of where the fact
should live. It is not a patch proposal.

## What comes from where

| part | source |
| --- | --- |
| `usize`, `u32` and `u64` model as `model::UInt`; a `UInt` value is refined with `v >= 0`, assumed where read and an obligation where produced, and conjoined to each template in `build_refined` | #268 |
| the fact at a value's root: parameter, return value, local, enum variant field | #268 |
| tuple-element refinements normalized in subtyping; pointee refinements kept through borrows, assignments, calls, branches and loops | #286 |
| the fact on tuple elements, struct fields and the content of `&T` and `&mut T` (`TypeBuilder::field_type`, `PointerType::*_to_refined`) | fork, `7976671f` |
| the fact as an invariant of a `&mut` content, and of the box of a local that the body borrows mutably (`is_mut_borrowed`, `mut_local_content` in `src/analyze/basic_block.rs`) | fork, `7976671f` |
| the fact on the content of the `Mut` model; soundness tests `tests/ui/fail/unsigned_soundness_*` (12) | fork, `2df4ee54` |

With the extension, `BitMatrix::rows`, `DenseBitSet::clear_excess_bits`, `Size::bits` and
`Size::checked_add` in `tests/ui/pass/rustc_coroutine/` verify without `#[thrust::trusted]`.

## Query sizes

Frontend only, with a stub solver that prints `sat`. Each test file is run with its own
`//@compile-flags` and `//@rustc-env`, from the root of a worktree after `cargo build --workspace`:

```sh
LD_LIBRARY_PATH=$(rustc --print sysroot)/lib THRUST_OUTPUT_DIR=<dir> THRUST_SOLVER=<stub> \
  THRUST_TRY_SPECS=1 target/debug/thrust-rustc --edition 2024 -Adead_code -C debug-assertions=off \
  -o <dir>/a.out tests/ui/pass/rustc_coroutine/univariant.rs
```

`f05d3dd2` is `main` before #268 and #286 were merged; `44b72fc6` is `main` with both and the
extension.

| query | `f05d3dd2` | `44b72fc6` | clauses with head `t >= 0` | of those, head is a conjunct of the body |
| --- | --- | --- | --- | --- |
| stage 3 `bitset.rs` | | 430 clauses, 1.8 MB | 320 | 286 |
| stage 5 `eligibility.rs` | 732 clauses, 6.7 MB | 2150 clauses, 35 MB | 1470 | 1391 |
| stage 6 `univariant.rs` | 1785 clauses, 20.5 MB | 11273 clauses, 743 MB | 9738 | 9655 |
| `creusot/counter_creusot.rs` | | 179 clauses | 90 | 81 |

Without the `t >= 0` heads, stage 5 has 680 clauses and stage 6 has 1535, so the specifications
added between the two commits account for little of the growth.

In stage 5, 107 of the 1470 heads are about a root variable, the positions #268 reaches. The other
1363 are about a projection: a field, a tuple element, or the current or final value of a
reference. These are the positions the extension adds. A typical clause:

```
(=> (and (>= (tuple_proj.2 v0) 0) ... (>= (tuple_proj.2 v11) 0) ... true)
    (>= (tuple_proj.2 v11) 0))
```

## Where the clauses come from

`relate_refined_type` (`src/rty/subtyping.rs`) makes the expected refinement the head, and
`ClauseBuilder::head` makes one clause per head atom, each with a copy of the whole body. A
refinement in a nested position travels with the value (#286), so every subtyping on a value with
k unsigned positions gives k clauses. In most of them the value on the left comes with the same
fact, so the clause holds as written.

## Solver

CoAR built from fptprove `develop` `96d99c747`, `pcsat_tbq_ar.json`, `-p pcsp`, 2 CPUs, 6 GB,
60 s cap:

| query | as emitted | clauses whose head is a body conjunct removed |
| --- | --- | --- |
| `bitset`, pass | `sat` 1.6 s, 1.7 s | `sat` 13.6 s |
| `bitset`, fail | `unsat` 6.8 s, 17.9 s | `unsat` 27.1 s |
| `eligibility` | killed at 6 GB, 54.7 s and 55.0 s | killed at 6 GB, 44.2 s |
| `univariant` | no answer at 60 s | not run |

Removing the clauses that hold as written does not help the solver, and slows `bitset`.

## Question

The fact holds for every value of an unsigned type. As a refinement, though, it is proved again at
each subtyping, and #286 carries it into every nested position. #268's description says the
complete fix needs unsignedness in `rty::Type` rather than in a refinement. In that form the fact
would be assumed wherever a value of the type enters the environment, and proved only where an
unsigned value is produced outside its range: unsigned `-` without overflow checks. Casts wrap,
and checked arithmetic stays in range. Flux works this way: `uint_invariants` gives unsigned types a
non-negativity invariant, and with overflow checking off, unsigned subtraction carries
`requires a - b >= 0` (`ConstrReason::Underflow`). The fork has not implemented this.
