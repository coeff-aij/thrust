# Narrowing probes for the two tests that stall

Eight hand-made variants of two ui tests, each narrowing the input one step so that the
reason a query does not finish can be attributed to a piece rather than guessed at. They
are kept here rather than under `tests/ui/`: they are not tests, nothing asserts anything
about them, and the ui harness only walks `tests/ui/`.

## `fuse_*` — one piece of the specification blanked at a time

Cut from `tests/ui/pass/traits/fuse.rs`, which does not finish. `Fuse::next` contains no
loop, so the cost is not loop reasoning; the query carries 15 dependent-existential
predicate variables over 3 forall-funs at arity up to 15, and substituting concrete
definitions for the forall-funs — which flattens the dependent existentials away — decides
it in about a second. Each probe weakens one `#[predicate]` body to `"true"`:

| probe | what it blanks |
| --- | --- |
| `fuse_inv_true` | `invariant` |
| `fuse_completed_true` | `completed` |
| `fuse_step_true` | `step` |
| `fuse_all_true` | `invariant` and `completed` together |
| `fuse_noexists` | only the `(exists ((i a0)) …)` inside `completed`, the rest of the body kept |

`fuse_noexists` is the one that isolates the dependent existentials themselves rather than
a whole predicate.

## `result_mut_*` — the program narrowed three ways

Cut from `tests/ui/pass/result_mut.rs`, which emits nothing in 300 s under the default
backend while Spacer answers both polarities in about 1.3 s.

| probe | what it narrows |
| --- | --- |
| `result_mut_inline` | the callee inlined into `main`, so no function boundary |
| `result_mut_one_arm` | `Err(e) => *e -= 1` weakened to `Err(_) => {}` |
| `result_mut_no_unreachable` | the trailing `match` + `unreachable!()` written as `if let Ok(v)` |

## Re-dumping one: put it back under the name it was cut from

**`fuse_*` must be dumped as `tests/ui/pass/traits/fuse.rs`, and `result_mut_*` as
`tests/ui/pass/result_mut.rs`.** These tests write some predicates as hand-written SMT
strings that spell the predicate's symbol out in full, and the symbol embeds the top half
of a `def_path_hash`, which hashes the **crate** name — which for a ui test is its file
name. Dump one of these probes under its own file name and every such string still names
the symbols of the crate it was cut from, and they are undeclared in the file being
emitted.

That is not hypothetical. A copy of `fuse_noexists` dumped under its own name produced a
query the SMT-LIB2 reader refused outright (`q_invariant_… is not bound`) and, before
reaching that, silently cost one predicate variable its dependency list — a plain
`declare-fun` where the correct dump has a `declare-dep-exists-fun`, so the probe would
have read as measuring one dependent existential fewer. The dump looked ordinary either
way.

The `.smt2` beside each `.rs` is that probe's dump, taken this way. The command is the one
in `benchmarks/DQpCSP/thrust_generated/TRAIT_PAIRS.md` of the CoAR repository:
`THRUST_OUTPUT_DIR` with a stub solver, so nothing is solved at dump time.

## Why they are here and not in the CoAR repository

They were committed there once, alongside the dumps of the tests they are cut from, and
taken back out. Everything in that corpus is the dump of a test that exists in
`tests/ui/`, so it can be regenerated and checked against its source; a probe is a test
edited by hand and has no such original, so a copy kept there would drift from this tree
with nothing to notice. Whatever is exported from here should be exported after a probe is
settled, not while it is being cut.
