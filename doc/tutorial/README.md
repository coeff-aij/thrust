# Thrust tutorial

A short, progressive introduction to verifying Rust programs with Thrust. Each chapter has one or
two small programs under [examples/](examples/), and every output shown was produced by running
them (abbreviated where long). The reference for every annotation and environment variable is the
[README](../../README.md); the tutorial links to it rather than restating it.

1. [Getting started](01-getting-started.md): building Thrust, the solvers, verifying one file.
2. [Contracts](02-contracts.md): `requires`, `ensures`, what the verdicts mean, contracts left to
   inference.
3. [Loops](03-loops.md): inferred invariants, and when to write `invariant!` or
   `partial_invariant!`.
4. [Mutable references](04-mutable-references.md): current and final values (prophecies).
5. [Traits and generics](05-traits-and-generics.md): contracts on trait methods, predicates, logic
   functions, laws, a generic function verified once.
6. [Iterators and `for`](06-iterators.md): `for` loops over the iterators `std.rs` specifies.
7. [Reading a failure](07-reading-a-failure.md): the report (`THRUST_REPORT`), counterexample
   values, inferred contracts, JSON for tools and agents.
8. [Verify, fix, verify again](08-incremental.md): `THRUST_SPLIT` and `THRUST_CACHE_DIR`.
9. [What is trusted, and the limits](09-trust-and-limits.md).

[scenarios.md](scenarios.md) lists twelve small debugging scenarios (a bug, what the report shows,
the fix) for demos, user studies and agent trials.

## The examples

The examples are plain files rather than ui tests: several of them are meant to time out or to
fail with one solver and pass with the other, which the ui tests' pass/fail convention does not
express, and a reader runs them with the same command the text shows.
[examples/check.sh](examples/check.sh) runs each one with the solver
[examples/expected.txt](examples/expected.txt) names and compares the outcome with the one the
tutorial shows; `check.sh -n` lists the runs without making them, and `THRUST_RUSTC` names the
`thrust-rustc` binary to run (default: the debug build of this checkout).

The outputs were taken on fork branch `incremental` at 170fdd2c, with z3 4.15.2 and PCSat built
from fptprove f7ddc51c0.
