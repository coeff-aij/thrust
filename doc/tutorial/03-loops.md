# 3. Loops

Thrust infers loop invariants: each loop head gets an unknown predicate over the variables live
there, and the solver finds it. You write an invariant when the solver does not find one in time,
or to state and check one on purpose.

## Inferred

[examples/03_loop_inferred.rs](examples/03_loop_inferred.rs):

```rust
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == 2 * n)]
fn double_by_loop(n: i64) -> i64 {
    let mut i = 0;
    let mut s = 0;
    while i < n {
        i += 1;
        s += 2;
    }
    s
}
```

z3 verifies it, and the report shows the invariant it found:

```console
$ THRUST_REPORT=1 thrust 03_loop_inferred.rs
note: thrust: loop in `double_by_loop`
 --> 03_loop_inferred.rs:6:11
  |
6 |     while i < n {
  |           ^^^^^
  |
  = note: invariant (inferred)
          double_by_loop.loop#1(n: int, i: int, s: int, old(n): int)
          := (2 * i = s ∧ 2 * old(n) >= s) ∨ (old(n) >= 0 ∧ n = old(n) ∧ i = 0 ∧ s = 0)
```

`double_by_loop.loop#1` is the first loop of `double_by_loop`, over the variables live at its
head; `old(n)` is the value `n` had on entry. The first disjunct says `s = 2 * i` and
`s <= 2 * old(n)`; the second is the state on entry.

## When the solver does not find it

The invariant of a sum needs a product ([examples/03_loop_sum.rs](examples/03_loop_sum.rs)):

```rust
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(2 * result == n * (n - 1))]
fn sum_below(n: i64) -> i64 {
    let mut i = 0;
    let mut s = 0;
    while i < n {
        s += i;
        i += 1;
    }
    s
}
```

z3 does not find it; PCSat does, in about a second:

```console
$ thrust 03_loop_sum.rs
...
error: verification error: Timeout(30s)

error: aborting due to 1 previous error; 1 warning emitted

$ THRUST_SOLVER=$THRUST/tests/thrust-pcsat-wrapper thrust 03_loop_sum.rs; echo "exit $?"
exit 0
```

Writing the invariant lets z3 check it instead of searching for it
([examples/03_loop_sum_invariant.rs](examples/03_loop_sum_invariant.rs)):

```rust
    while i < n {
        thrust_macros::invariant!(|i: i64, s: i64, n: thrust_models::FnParam<i64>|
            0 <= i && i <= n.at_entry() && 2 * s == i * (i - 1));
        s += i;
        i += 1;
    }
```

```console
$ thrust 03_loop_sum_invariant.rs; echo "exit $?"
exit 0
```

- `invariant!` goes at the start of the loop body. The closure's parameters name the variables
  live at the loop head; a `thrust_models::FnParam<T>` parameter names a function parameter, read
  at entry with `.at_entry()`.
- A written invariant is the whole invariant: nothing is inferred at that loop, so it has to state
  everything the rest of the function needs (here `i <= n`, which gives `i = n` at the exit).
- It is checked, not assumed: it must hold on entry and be preserved by the body.

## Partial invariants

`partial_invariant!` takes the same closure and is conjoined with what Thrust infers at the loop,
so you write only the fact the solver misses
([examples/03_loop_sum_partial.rs](examples/03_loop_sum_partial.rs)):

```rust
        thrust_macros::partial_invariant!(|i: i64, s: i64| 2 * s == i * (i - 1));
```

With PCSat this verifies (exit 0, about a second); z3 still times out at 30 s, since it still has
to search for the rest of the invariant. With z3, write the full `invariant!`.

## A wrong invariant

[scenarios/s05_invariant_not_preserved.rs](examples/scenarios/s05_invariant_not_preserved.rs)
writes `i * (i + 1)` for `i * (i - 1)`:

```console
$ THRUST_REPORT=1 thrust s05_invariant_not_preserved.rs
...
error: verification error: Unsat (thrust: refuted: loop preservation in `sum_below`)
  --> s05_invariant_not_preserved.rs:6:5
   |
 6 | /     while i < n {
 7 | |         thrust_macros::invariant!(|i: i64, s: i64, n: thrust_models::FnParam<i64>|
 8 | |             0 <= i && i <= n.at_entry() && 2 * s == i * (i + 1));
   | |             --------------------------------------------------- the annotation it checks
 9 | |         s += i;
10 | |         i += 1;
11 | |     }
   | |_____^
   |
   = note: c2: (__tmp_mir_sum_below_7 < n ∧ s = *__tmp_mir_sum_below_8 + __tmp_mir_sum_below_7 ∧ i = __tmp_mir_sum_below_7 + 1 ∧ 0 <= __tmp_mir_sum_below_7 ∧ __tmp_mir_sum_below_7 <= n ∧ 2 * *__tmp_mir_sum_below_8 = __tmp_mir_sum_below_7 * (__tmp_mir_sum_below_7 + 1)) ==> ((0 <= i ∧ i <= n) ∧ 2 * s = i * (i + 1))
   = note: where it fails: n = 1, __tmp_mir_sum_below_7 = 0, *__tmp_mir_sum_below_8 = 0, s = 0, i = 1
   = note: the solver refutes one obligation of a query: others may fail too (`THRUST_SPLIT` refutes one in each part)

error: aborting due to 1 previous error; 1 warning emitted
```

`loop preservation` says the body does not keep the invariant. In the constraint,
`__tmp_mir_sum_below_7` and `*__tmp_mir_sum_below_8` are `i` and `s` before the iteration, `i` and
`s` after it: from `i = 0, s = 0` (where the invariant holds, `0 = 0 * 1`) the body reaches
`i = 1, s = 0`, where `2 * 0 = 1 * 2` is false. The refutation is the error, at the loop with the
written invariant labelled, so an editor shows it there.

Loops written with `for` are in [chapter 6](06-iterators.md).
