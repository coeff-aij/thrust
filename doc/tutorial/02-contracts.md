# 2. Contracts

A contract states what a function needs (`requires`) and what it guarantees (`ensures`). Both are
ordinary Rust expressions over the parameters; in `ensures`, `result` is the return value. All
examples here run with z3.

[examples/02_withdraw.rs](examples/02_withdraw.rs):

```rust
#[thrust_macros::requires(amount <= balance)]
#[thrust_macros::ensures(result == balance - amount)]
fn withdraw(balance: i64, amount: i64) -> i64 {
    balance - amount
}

#[thrust_macros::ensures(result >= 0)]
#[thrust_macros::ensures(result == x || result == -x)]
fn abs(x: i64) -> i64 {
    if x < 0 {
        -x
    } else {
        x
    }
}

fn main() {
    let b = withdraw(100, 30);
    assert!(b == 70);
    assert!(abs(-5) == 5);
}
```

```console
$ thrust 02_withdraw.rs; echo "exit $?"
exit 0
```

Thrust checks each body against its contract once, and each call against the callee's contract:
the caller must establish `requires`, and may use only `ensures` afterwards. Several `ensures` (or
`requires`) are conjoined; a missing one is `true`. `==` in a contract compares values logically
and needs no `PartialEq`.

A call that breaks a precondition ([examples/02_withdraw_overdraw.rs](examples/02_withdraw_overdraw.rs),
`withdraw(10, 30)`) fails:

```console
$ thrust 02_withdraw_overdraw.rs; echo "exit $?"
error: verification error: Unsat

error: aborting due to 1 previous error

exit 1
```

## What the verdicts mean

| Output | Exit | Meaning |
|---|---|---|
| nothing | 0 | safe: no assertion fails, nothing panics, every contract holds |
| `verification error: Unsat` | 1 | no refinement typing exists for the program with the contracts written |
| `verification error: Timeout(30s)` | 1 | unknown: the solver did not answer in time |
| `verification error: Error { .. }` or `Unknown` | 1 | unknown: the solver gave up or could not read the query |

`Unsat` is not always a bug in the code: the contracts you wrote are part of the question. A
postcondition too weak for a caller ([scenario 8](scenarios.md)), or a written loop invariant that
is not inductive, also gives `Unsat`. [Chapter 7](07-reading-a-failure.md) shows how to tell
which obligation fails.

## Contracts left to inference

A function without `requires`/`ensures` gets its contract inferred from its body and its callers.
[examples/02_inferred.rs](examples/02_inferred.rs):

```rust
fn double(x: i64) -> i64 {
    x + x
}

fn main() {
    let y = double(3);
    assert!(y == 6);
}
```

`THRUST_REPORT=1` shows what was inferred:

```console
$ THRUST_REPORT=1 thrust 02_inferred.rs
note: thrust: `double`
 --> 02_inferred.rs:1:1
  |
1 | fn double(x: i64) -> i64 {
  | ^^^^^^^^^^^^^^^^^^^^^^^^
  |
  = note: contract (inferred)
          inferred: fn double(x: {int | x = 3}) -> {int | result = 6 ∧ x = 3}
```

The inferred contract is a refinement type: `{int | x = 3}` is an integer satisfying `x = 3`. It
is only as general as the callers need: `double` is checked for the argument `main` passes, not
for every `i64`. Two consequences:

- A function that no analyzed function calls, and that has no contract, is not checked at all.
  Mark an entry point with `#[thrust::callable]` (short for `requires(true)` and `ensures(true)`)
  to check it for every argument:

  ```console
  $ cat 02_uncalled.rs
  fn f(x: i64) {
      assert!(x > 0);
  }

  fn main() {}
  $ thrust 02_uncalled.rs; echo "exit $?"
  warning: function `f` is never used
   --> 02_uncalled.rs:1:4
    |
  1 | fn f(x: i64) {
    |    ^
    |
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

  warning: 1 warning emitted

  exit 0
  $ thrust 02_uncalled_callable.rs; echo "exit $?"    # the same with #[thrust::callable] on f
  warning: function `f` is never used
  ...
  error: verification error: Unsat

  error: aborting due to 1 previous error; 1 warning emitted

  exit 1
  ```

  rustc's warning that `f` is never used is the hint: Thrust checks only what is called or
  marked.

- A bug in a function left to inference shows up at its caller ([scenario 4](scenarios.md)).

Write a contract where the function is an interface (called from many places, or part of an
API), and leave small helpers to inference.

## Trusted functions

`#[thrust::trusted]` skips the body and assumes the contract. It is how a test models input:

```rust
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}
```

Everything a trusted contract says is assumed, so keep such functions few
([chapter 9](09-trust-and-limits.md)).

Refinement types can also be written directly (`#[thrust_macros::param]`, `ret`, `sig`); see
[Refinement types](../../README.md#refinement-types).
