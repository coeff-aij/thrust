# Unsigned integers are not constrained as non-negative

## Status

Provisional fix on this fork's branch `unsigned-nonneg` (`022b28c`, plus a test-only follow-up
`bb174e5`, both pushed). Upstream is working a more general fix on unmerged branches; this
fork's fix is meant to be replaced by that, not proposed as the final design.

## Symptom

Thrust maps every integer type to the logic sort `Int`; nothing in the emitted clauses stated
that a value of an unsigned Rust type (`usize`, `u8`, `u16`, ...) cannot be negative. A loop over
a `usize` counter that runs while the counter is nonzero then has a reachable logical state at a
negative value that no execution of the program reaches, and a written invariant such as
`self.n >= 0` cannot be concluded from a `usize` parameter alone.

## What the fork branch adds

`FunctionTemplateTypeBuilder::build` (`src/refine/template.rs`) adds the fact `x >= 0` for each
parameter `x` of unsigned type, and `v >= 0` for a result of unsigned type. It applies to both
function signatures and basic-block types, so it covers function parameters and results (extern
specs, trusted functions and trait method declarations included), the live locals a basic block
carries at a loop header or join point, and the outer-function parameter copies those blocks
carry. A written `invariant!` is conjoined to the block's facts rather than replacing them. The
fact is assumed where the type is entered and proved where it is left (at calls, at jumps to a
block with its own precondition, and at returns).

Not covered: struct fields, the referent of `&`/`&mut` (a `&mut` final value is a prophecy the
caller cannot establish), `Box`, sequence and enum contents, fields of a hand-written model such
as a tuple, and closure parameters seen only through an `Fn` bound. Covering fields and the
current value of references was tried; it changed neither of the two motivating queries below
and refuted `tests/ui/pass/rustc_coroutine/values.rs`, so it is not in the fix.

Two extern-spec `requires` were added on this same branch (`bb174e5`) because their model fields
carry no fact of their own: `WordIter::next`'s `(*it).1 >= 0` and `IdxRange::next`'s
`(*it).start >= 0`, both in `tests/ui/pass/rustc_coroutine/idx.rs`.

## The two queries that motivated it

fptprove `thrust-benchmarks` (origin, commit `eaa661e78`),
`benchmarks/DQpCSP/thrust_generated/unsolved/unsigned_nonneg/`:

- `skip_next_sat.smt2` was `unsat` through a `usize` skip count going to `-1`
  (`docs/SKIP_NEXT_PLAN.md` §3 in that repository).
- `take_disjunct_min_sat.smt2`, B5's minimal core, had the same obstruction in the nested
  `Skip`/`Take` state, with the loop parameter `n: usize` unconstrained below zero.

At Thrust `8a187ff` (before the fix) both were `unsat,0`, which rested on the negative-`usize`
witness rather than on the property being proved. At `bb174e5` (with the fix) the minimal core
flips to `sat,0` -- the negative-`usize` witness is gone -- while the full `take_disjunct` query
gets no answer within its time cap either before or after; only the refutation that rested on the
missing fact changed. `skip_next_sat` stays `unsat` at both commits for an unrelated reason (a
gap in the generic `Skip<I>` proof, not the `usize` bound), recorded in that same directory's
`README.md`.

## Upstream's general fix

Upstream `main` currently constrains only unsigned constants as unsigned (#277). An earlier,
unmerged upstream branch `claude/great-galileo-1zj0z2` (`46c0d0d`) modeled `usize`/`u*` as a
distinct `UInt` sort, but predates native sequences and Rust-syntax predicates. Upstream's
current in-progress work is four unmerged branches (`git ls-remote upstream
'refs/heads/claude/vibrant-brown*'`, verified present):

- `claude/vibrant-brown-tjmb6h-int-range`
- `claude/vibrant-brown-tjmb6h-wrapping`
- `claude/vibrant-brown-tjmb6h-checked-arith`
- `claude/vibrant-brown-tjmb6h-bigint`

dated 2026-09-24 from base `ff4f51a`, which give every integer type range facts and wrapping
arithmetic -- a general fix, in contrast to this fork's narrower "unsigned parameters and results
only" patch. This fork's `unsigned-nonneg` branch exists to unblock the two queries above ahead of
that landing, not as a competing design.
