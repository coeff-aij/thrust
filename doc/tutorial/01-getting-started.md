# 1. Getting started

Thrust is a refinement type checker for Rust. It reads a crate the way `rustc` does, turns the
question "can this program panic, or break a contract?" into constrained Horn clauses (CHCs), and
asks a CHC solver whether they have a solution. A solution is a refinement typing of the program:
contracts and loop invariants that Thrust did not need you to write.

## Building

Thrust is built from source with the toolchain its `rust-toolchain.toml` pins
(`nightly-2025-09-08`):

```sh
git clone https://github.com/coeff-aij/thrust && cd thrust
cargo build --bin thrust-rustc
```

`thrust-rustc` behaves like `rustc`. Outside `cargo run` it needs the toolchain's libraries on
`LD_LIBRARY_PATH`. The rest of the tutorial uses this shell function:

```sh
THRUST=$PWD    # the Thrust checkout
thrust() {
  LD_LIBRARY_PATH="$(rustc +nightly-2025-09-08 --print sysroot)/lib" \
    "$THRUST/target/debug/thrust-rustc" -C debug-assertions=off "$@"
}
```

`-C debug-assertions=off` turns off rustc's overflow checks, which Thrust does not support; how
integer ranges are treated is in [chapter 9](09-trust-and-limits.md). rustc's own warnings on the
program (an unused variable, a function never called) are printed as usual; the outputs in this
tutorial leave them out where they say nothing about verification.

Like `rustc`, `thrust-rustc` also compiles the program (add `--out-dir` to put the binary
elsewhere). A Cargo project without dependencies is checked by setting `RUSTC` to the binary; see
[Using Thrust with Cargo](../../README.md#using-thrust-with-cargo).

## Solvers

Thrust needs a CHC solver. Two are used:

- z3 (the default, `THRUST_SOLVER` unset): fast, on your `PATH`. It cannot read the parts of a
  query that sequences, quantified functions and generic code produce, and on the loop of
  [chapter 3](03-loops.md) whose invariant needs a product it times out. Only z3 gives the report its solutions and
  counterexamples ([chapter 7](07-reading-a-failure.md)).
- PCSat, from [CoAR](https://github.com/hiroshi-unno/coar): needed for `Vec`, slices, iterators,
  predicates over generic types and laws. Thrust runs it in Docker through
  [tests/thrust-pcsat-wrapper](../../tests/thrust-pcsat-wrapper). Build an image from CoAR's
  `Dockerfile` and name it with `COAR_IMAGE` (the wrapper's default is `coar:latest`):

  ```sh
  export THRUST_SOLVER=$THRUST/tests/thrust-pcsat-wrapper
  export COAR_IMAGE=coar:latest
  ```

  The wrapper mounts the current directory into the container, so run Thrust from the directory
  that holds the file.

`THRUST_SOLVER_TIMEOUT_SECS` bounds each solver run (default 30). Each chapter says which solver
its examples need; when z3 suffices, use it.

## A first run

[examples/01_add.rs](examples/01_add.rs):

```rust
fn add(x: i64, y: i64) -> i64 {
    x + y
}

fn main() {
    assert!(add(1, 2) == 3);
}
```

```console
$ thrust 01_add.rs; echo "exit $?"
exit 0
```

No output and exit status 0: Thrust found that no `assert!` can fail and nothing can panic. Break
the assertion ([examples/01_add_wrong.rs](examples/01_add_wrong.rs), `== 2`):

```console
$ thrust 01_add_wrong.rs; echo "exit $?"
error: verification error: Unsat

error: aborting due to 1 previous error

exit 1
```

`Unsat` means the constraints have no solution: no typing shows the program safe. The next
chapter says what that does and does not mean, and [chapter 7](07-reading-a-failure.md) how to
see why.

With PCSat the verdicts are the same (each run starts a container, here about a second):

```console
$ THRUST_SOLVER=$THRUST/tests/thrust-pcsat-wrapper thrust 01_add.rs; echo "exit $?"
exit 0
```

When z3 meets a query it cannot read, the run ends with its raw parse errors, for example on the
`for` loop of [chapter 6](06-iterators.md), and a help line says how to run PCSat instead:

```console
$ thrust 06_for_range.rs
error: verification error: Error { stdout: "(error \"line 48 column 87: unknown sort 'Seq'\")\n(error \"line 71 column 911: unknown constant seq.unit (Int) \")\nsat\n", stderr: "" }
  |
  = help: the query has forall sorts or sequences, which `z3` does not read; PCSat, the CHC solver of CoAR, does: set `THRUST_SOLVER` to the PCSat wrapper of Thrust (`tests/thrust-pcsat-wrapper` in its repository), which runs the CoAR image `COAR_IMAGE` in Docker

error: aborting due to 1 previous error
```

The help comes only when z3's answer has such `(error` lines; with `THRUST_SPLIT`
([chapter 8](08-incremental.md)), only on the parts that have them.
