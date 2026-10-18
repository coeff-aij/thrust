# 9. What is trusted, and the limits

A `safe` verdict means: under the assumptions below, no assertion fails, nothing panics, and every
written contract holds whenever the function returns. The reference for each item is the
[README](../../README.md); this chapter lists what to keep in mind.

## Assumed, not checked

- The contracts of `#[thrust::trusted]` functions ([Annotation](../../README.md#annotation)).
- The specifications of the standard library in [std.rs](../../std.rs), which Thrust injects into
  every crate it checks. Their bodies are not analyzed there; the laws of its spec traits are
  checked once by a ui test (see [Development](../../README.md#development)).
- The contracts of the methods rustc's `#[derive(..)]`s generate, as the paragraph on derives in
  [Annotation](../../README.md#annotation) states them.
- Under `THRUST_VERIFY_ONLY`, the written contracts of the functions outside the selection
  ([Verifying part of a crate](../../README.md#verifying-part-of-a-crate)).
- With `THRUST_CACHE_DIR`, the verdicts kept from earlier runs: a query is keyed by its text, the
  solver command and `THRUST_CACHE_SALT`, so a solver wrapper whose image changes needs the salt
  ([chapter 8](08-incremental.md)).
- The solver's verdict. z3 runs with `fp.validate=true` by default; for PCSat, see
  [CoAR](https://github.com/hiroshi-unno/coar).

## Not what the verdict says

- Termination. A function that never returns satisfies any postcondition, and a caller of it
  never reaches what follows. [examples/09_spin.rs](examples/09_spin.rs) verifies:

  ```rust
  fn spin() -> i64 {
      loop {}
  }

  fn main() {
      assert!(spin() == 1);
  }
  ```

  Only lemmas and recursive logic functions are checked to terminate (their `variant`).
- Integer overflow, by default. Integers are mathematical, and rustc's overflow checks must be
  off (`-C debug-assertions=off`). [examples/09_overflow.rs](examples/09_overflow.rs) verifies,
  although `x + 1` overflows at `i64::MAX`:

  ```rust
  #[thrust::callable]
  fn next(x: i64) -> i64 {
      let y = x + 1;
      assert!(y > x);
      y
  }
  ```

  ```console
  $ thrust 09_overflow.rs; echo "exit $?"
  ...
  exit 0
  $ THRUST_INT_RANGE=all thrust 09_overflow.rs; echo "exit $?"
  ...
  error: verification error: Unsat

  error: aborting due to 1 previous error; 1 warning emitted

  exit 1
  ```

  `THRUST_INT_RANGE=conversions` assumes each value in its type's range and checks conversions;
  `all` also checks `+`, `-`, `*` ([Configuration](../../README.md#configuration)).
- The body of a function that has no contract and that no analyzed function calls
  ([chapter 2](02-contracts.md)).

## Not supported yet

- Crates with dependencies (Cargo projects without dependencies work:
  [Using Thrust with Cargo](../../README.md#using-thrust-with-cargo)).
- Parts of the standard library without a specification in `std.rs`. A call to one stops Thrust
  rather than being assumed to do anything; [examples/09_no_spec.rs](examples/09_no_spec.rs)
  calls `i64::pow`:

  ```console
  $ thrust 09_no_spec.rs; echo "exit $?"
  error: thrust: no specification of `core::num::<impl i64>::pow`, which `main` calls
   --> 09_no_spec.rs:2:13
    |
  2 |     let x = 3i64.pow(2);
    |             ^^^^^^^^^^^
    |
    = help: give the call a contract: call it through a function marked `#[thrust::trusted]` with `requires` and `ensures`, or write a specification of it as Thrust's `std.rs` does (`#[thrust::extern_spec_fn]`)

  error: aborting due to 1 previous error

  exit 1
  ```

  A wrapper marked `#[thrust::trusted]` with a contract is the way around it. Other unsupported
  constructs may also stop Thrust with an error or a panic; that is expected while Thrust is
  developed ([AGENTS.md](../../AGENTS.md)).
- Models and inferred contracts from PCSat: the report's inferred contracts and loop invariants
  need z3, and so does a failure's refutation, which z3 gives for a query PCSat refutes only when
  it can read it ([chapter 7](07-reading-a-failure.md)).

The ui tests in [tests/ui/pass](../../tests/ui/pass) and [tests/ui/fail](../../tests/ui/fail) are
the most complete list of what Thrust handles today.
