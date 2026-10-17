# 7. Reading a failure

`verification error: Unsat` says that something fails, not what. `THRUST_REPORT=1` adds, as
compiler notes at the code they belong to, the obligation the solver refuted, the values where it
fails, and the run that reaches it; on success, it shows the contracts and loop invariants Thrust
inferred. The failure and the inferred contracts need z3, the default solver.

The program of this chapter and the next, [examples/08_shop_1.rs](examples/08_shop_1.rs), has
three bugs:

```rust
#[thrust_macros::requires(amount <= balance)]
#[thrust_macros::ensures(result == balance - amount)]
fn withdraw(balance: i64, amount: i64) -> i64 {
    balance - amount - 1                       // bug: - 1
}

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == 3 * n)]
fn shipping(n: i64) -> i64 {
    let mut i = 0;
    let mut cost = 0;
    while i <= n {                             // bug: <= for <
        cost += 3;
        i += 1;
    }
    cost
}

fn price(units: i64) -> i64 {                  // no contract: inferred
    if units > 10 {                            // bug: > for >=
        units * 9
    } else {
        units * 10
    }
}

fn main() {
    let p = price(10);
    assert!(p == 90);
    let left = withdraw(200, p);
    assert!(left == 110);
    assert!(shipping(2) == 6);
}
```

(The comments are not in the file.) The examples below copy it to `shop.rs` first.

## The refuted obligation

```console
$ THRUST_REPORT=1 thrust shop.rs
note: thrust: refuted: ensures in `withdraw`
 --> shop.rs:5:2
  |
2 | #[thrust_macros::ensures(result == balance - amount)]
  |                          -------------------------- the annotation it checks
...
5 | }
  |  ^
  |
  = note: c0: (result = __tmp_mir_withdraw_3 - 1 ∧ __tmp_mir_withdraw_3 = balance - amount ∧ withdraw.bb0 balance amount balance amount) ==> result = balance - amount
  = note: where it fails: result = -1, balance = 0, amount = 0, __tmp_mir_withdraw_3 = 0
  = note: how the solver reaches it: each fact follows, by the constraint in brackets, from the facts indented under it (a derivation, not an order of execution):
            withdraw.bb0(balance = 0, amount = 0, old(balance) = 0, old(amount) = 0)   [c1 function entry, shop.rs:3:1]
  = note: the solver refutes one obligation of a query: others may fail too (`THRUST_SPLIT` refutes one in each part)

error: verification error: Unsat
 --> shop.rs:5:2
  |
5 | }
  |  ^

error: aborting due to 1 previous error
```

- The title names what is checked (`ensures`, `assertion`, `precondition of f`,
  `loop preservation`, `argument of f`, ...) and in which function. The span is where it is
  checked, for `ensures` the end of the body; the label marks the annotation checked there (each
  clause, "a clause of the annotation it checks", when there are several: the refutation does not
  say which one fails). The error is at the same place, so an editor shows it there.
- `c0:` is the constraint: premises `==>` conclusion, over the program's variables.
  `__tmp_mir_withdraw_3` is a value the program does not name (here `balance - amount`).
- `where it fails` gives values that make the premises true and the conclusion false: one
  counterexample, chosen by the solver.
- The run is how the solver derived the premises: each fact above the facts it follows from, with
  the constraint and the code that produced it. `withdraw.bb0` is the state at the function's
  first block.

The last note says that this is the first failure only: one query has one refutation. Solving in
parts (chapter 8) shows one per failing part:

```console
$ THRUST_SPLIT=4 THRUST_REPORT=1 thrust shop.rs
note: thrust: refuted: ensures in `withdraw`
...
note: thrust: refuted: ensures in `shipping`
  --> shop.rs:17:2
   |
 8 | #[thrust_macros::ensures(result == 3 * n)]
   |                          --------------- the annotation it checks
...
17 | }
   |  ^
   |
   = note: c3: (shipping.loop#1 n i cost n ∧ i > n) ==> cost = 3 * n
   = note: where it fails: cost = 3, n = 0, i = 1
   = note: how the solver reaches it: each fact follows, by the constraint in brackets, from the facts indented under it (a derivation, not an order of execution):
             shipping.loop#1(n = 0, i = 1, cost = 3, old(n) = 0)   [c4 loop preservation, shop.rs:12:5]
               shipping.loop#1(n = 0, i = 0, cost = 0, old(n) = 0)   [c2 loop entry, shop.rs:12:5]
                 shipping.bb0(n = 0, old(n) = 0)   [c5 function entry, shop.rs:9:1]

note: thrust: refuted: assertion in `main`
  --> shop.rs:29:5
   |
29 |     assert!(p == 90);
   |     ^^^^^^^^^^^^^^^^
   |
   = note: c19: main.price#1 p ==> p = 90
   = note: where it fails: p = 100
   = note: how the solver reaches it: each fact follows, by the constraint in brackets, from the facts indented under it (a derivation, not an order of execution):
             main.price#1(p = 100)   [c11 after call to `price`, shop.rs:28:13]
               price.post(units = 10, result = 100)   [c8 return value, shop.rs:25:2]
                 price.bb3(result = 100, units = 10)   [c6 jump to bb3, shop.rs:20:5]
                   price.bb0(units = 10, old(units) = 10)   [c9 function entry, shop.rs:19:1]
                     price.pre(units = 10)   [c10 argument of `price`, shop.rs:28:13]
   = note: it goes through the contract inferred for `price`: a wrong result there shows here

error: verification error: Unsat
 --> shop.rs:5:2
...
   = note: in part 2 of 3, of 16 clauses from `price` (shop.rs:19-25), `main` (shop.rs:27-33)

note: thrust: 3 parts solved on their own, 0 of them from earlier runs

error: aborting due to 3 previous errors
```

- In `shipping` the run is one fact per loop iteration: from `n = 0` the loop runs once
  (`i <= n` with `i = 0`), so `cost = 3` where `3 * n = 0`.
- In `main` the bug is in `price`, whose contract is inferred: the failure shows at the caller,
  and the run goes down into `price` (`price.post(units = 10, result = 100)`), through the branch
  that produced 100 (`price.bb3`). When the run instead goes through a call to a function with a
  written contract, the note names it: `it assumes the written contract of `abs` (...): a wrong
  `ensures` there shows here` ([scenario 8](scenarios.md)).
- Each error names its part: its number (from 0), its size, and the functions its clauses come
  from with their lines.

## Inferred contracts

With every bug fixed ([examples/08_shop_4.rs](examples/08_shop_4.rs)), the same variable shows
what was inferred:

```console
$ THRUST_REPORT=1 thrust shop.rs
note: thrust: loop in `shipping`
  --> shop.rs:12:11
   |
12 |     while i < n {
   |           ^^^^^
   |
   = note: invariant (inferred)
           shipping.loop#1(n: int, i: int, cost: int, old(n): int)
           := (3 * i = cost ∧ 3 * old(n) - cost > -1) ∨ (old(n) >= 0 ∧ n = old(n) ∧ i = 0 ∧ cost = 0)

note: thrust: `price`
  --> shop.rs:19:1
   |
19 | fn price(units: i64) -> i64 {
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: contract (inferred)
           inferred: fn price(units: {int | units = 10}) -> {int | result = 90 ∧ units = 10}
```

`THRUST_REPORT` also takes a list of items: `template` (the unknowns before solving),
`constraints`, `solution`, `inferred`, `failure`, `internal`, `all`. On
[examples/02_inferred.rs](examples/02_inferred.rs):

```console
$ THRUST_REPORT=template,constraints,solution,inferred thrust 02_inferred.rs
note: thrust: `double`
 --> 02_inferred.rs:1:1
  |
1 | fn double(x: i64) -> i64 {
  | ^^^^^^^^^^^^^^^^^^^^^^^^
  |
  = note: contract (inferred)
          template: fn double(x: {int | double.pre x}) -> {int | double.post x result}
          solution: double.pre x := x = 3
                    double.post x result := result = 6 ∧ x = 3
          inferred: fn double(x: {int | x = 3}) -> {int | result = 6 ∧ x = 3}
  = note: constraints from this code:
            c0 return value (02_inferred.rs:3:2): (result = x + x ∧ double.bb0 x x) ==> double.post x result
            c1 function entry (02_inferred.rs:1:1): double.pre x ==> double.bb0 x x

note: thrust: `main`
 --> 02_inferred.rs:5:1
  |
5 | fn main() {
  | ^^^^^^^^^
  |
  = note: constraints from this code:
            c2 argument of `double` (02_inferred.rs:6:13): double.pre 3
            c3 after call to `double` (02_inferred.rs:6:13): double.post 3 y ==> main.double#1 y
            c4 return value (02_inferred.rs:8:2): (main.double#1 y ∧ y = 6) ==> main.post
            c5 assertion (02_inferred.rs:7:5): main.double#1 y ==> y = 6
            c6 function entry (02_inferred.rs:5:1): main.bb0
```

`THRUST_REPORT_ONLY=<paths>` limits the report to some functions, written as for
`THRUST_VERIFY_ONLY`.

## Names

| Name | Stands for |
|---|---|
| `f.pre`, `f.post` | the contract of `f`, when it is inferred; arguments in parameter order, `result` last |
| `f.loop#k` | the invariant of the `k`-th loop of `f` |
| `f.g#k r ...` | the result `r` of the `k`-th call to `g` in `f` |
| `f.bb3` | the state at block 3 of `f`'s MIR |
| `old(x)` | the value of parameter `x` on entry |
| `*r`, `°r` | the current and the final value of a `&mut` (in a constraint's unknowns, the pair `<*r, °r>`) |
| `…` | in a run's fact, the arguments the program does not name |
| `__tmp_mir_f_3` | a value the program does not name (local `_3` of `f`'s MIR) |
| `x@2` | the second variable `f` names `x` |

The full list is in [Reading what Thrust infers](../../README.md#reading-what-thrust-infers).

## JSON, for tools and agents

`THRUST_REPORT_FORMAT=json` writes the same report as JSON lines to `THRUST_REPORT_FILE` (default
standard output). The first line is a header (the format version, `root`, the absolute directory
the spans' files are relative to, and `columns`, the column unit: `1-based, in characters;
end_column after the last`); the second is the verdict; then, with `THRUST_SPLIT`, one `part` line
per part, and one `failure` line per refuted obligation (or, on success, a `site` line per
inferred contract and loop invariant).

```console
$ THRUST_SPLIT=4 THRUST_REPORT=1 THRUST_REPORT_FORMAT=json THRUST_REPORT_FILE=report.jsonl thrust shop.rs
error: verification error: Unsat
...
$ sed -n 2,3p report.jsonl
{"kind":"verdict","verdict":"unsat","refutations":"one per part"}
{"kind":"part","id":0,"clauses":2,"functions":[{"fn":"withdraw","span":{"file":"shop.rs","line":3,"column":1,"end_line":5,"end_column":2}}],"verdict":"unsat","cached":false}
$ jq -c 'select(.kind == "failure" and .fn == "main") | {part, obligation, span, conclusion, values, inferred, assumes}' report.jsonl
{"part":2,"obligation":"assertion","span":{"file":"shop.rs","line":29,"column":5,"end_line":29,"end_column":21},"conclusion":"p = 90","values":[{"name":"p","value":"100"}],"inferred":["price"],"assumes":[]}
```

A span is a range. A `failure` also has its `premises`, its `annotation` (the spans of the
annotation it checks), and its `run`, each step with the constraint's obligation and span;
`inferred` lists the functions left to inference that the run goes through, `assumes` the written
contracts it relies on.

## With PCSat

PCSat gives verdicts but no refutation or model yet, so the report says:

```console
note: thrust: no failing obligation to show: the solver gave no refutation (only `z3` is asked for one)
```

Two things still help. `THRUST_SPLIT` names the functions of each failing part, with their lines,
and puts the error at the code of the part. For the law of [scenario 10](scenarios.md):

```console
$ THRUST_SPLIT=4 THRUST_REPORT=1 thrust s10_law_fails_at_impl.rs
...
note: thrust: no failing obligation to show: the solver gave no refutation (only `z3` is asked for one)

error: verification error: Unsat
  --> s10_law_fails_at_impl.rs:40:5
   |
40 |     fn count_nonneg(c: &Clicks) {}
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: in part 1 of 4, of 2 clauses from `<Clicks as Counter>::count_nonneg` (s10_law_fails_at_impl.rs:40)
...
```

Then `THRUST_REPORT=constraints` with `THRUST_REPORT_ONLY` shows the constraints of those
functions, here the obligation the law puts on the impl:

```console
$ THRUST_REPORT=constraints THRUST_REPORT_ONLY='Clicks::count_nonneg' thrust s10_law_fails_at_impl.rs
...
note: thrust: `<Clicks as Counter>::count_nonneg`
  --> s10_law_fails_at_impl.rs:40:5
   |
40 |     fn count_nonneg(c: &Clicks) {}
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: constraints from this code:
             c4 ensures (s10_law_fails_at_impl.rs:40:35): <Clicks as Counter>::count_nonneg.bb0 c c ==> <Clicks as Counter>::count(c) >= 0
             c5 function entry (s10_law_fails_at_impl.rs:40:5): <Clicks as Counter>::count_nonneg.bb0 c c

error: verification error: Unsat

error: aborting due to 1 previous error; 2 warnings emitted
```
