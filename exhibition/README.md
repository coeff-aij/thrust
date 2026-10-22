# Exhibition demo

Verifies short programs with Thrust and PCSat from a terminal and shows the report. This branch
merges `report-pcsat-trace` (the obligation PCSat refutes) and `report-pcsat-model` (the
invariants PCSat infers) into `main`.

## Setup

```sh
cargo build                              # at the repository root
docker image inspect coar:latest > /dev/null  # the CoAR image the PCSat wrapper uses
```

## Commands

```sh
cd exhibition
./run.sh account.rs        # a bank account: verified
./run.sh account_bug.rs    # the balance check forgotten: withdraw's precondition fails
./run.sh savings.rs        # savings: the loop invariant, not written, is inferred
./run.sh savings_bug.rs    # a negative monthly amount allowed: the ensures fails
```

Each takes one or two seconds. Let the output reach the terminal whole: cutting it with `head`
closes the pipe and Thrust aborts.

## Reading the output

- `invariant (inferred)`: the loop invariant Thrust infers.
- `error: ... refuted: ...`: the specification that fails, `^^^` where it fails and `---` the
  annotation it checks.
- `c0: ...` and `reaching it (PCSat)`: the refuted constraint and the states reaching it, in
  PCSat's notation.
- `checked (sat)` / `checked (unsat)`: the result of each function.

## Limits

- An inferred invariant is shown only for programs over integers, Booleans and arrays: PCSat's
  solution printer has no forall sorts, so `account.rs` shows none.
- The variable names in `reaching it (PCSat)` may be out of order (`savings_bug.rs` shows
  `month = old(amount)`, which no run reaches).
