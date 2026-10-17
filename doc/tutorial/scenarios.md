# Debugging scenarios

Twelve small programs, each with one bug, for demos, user studies and trials with coding agents.
Each is a file under [examples/scenarios/](examples/scenarios/) with its fix next to it
(`*_fixed.rs`, which verifies).

Every scenario was run as

```sh
THRUST_SPLIT=4 THRUST_REPORT=1 thrust <file>
```

with z3, or with PCSat (`THRUST_SOLVER=$THRUST/tests/thrust-pcsat-wrapper`,
`THRUST_SOLVER_TIMEOUT_SECS=60`) where the table says so. The report lines below are copied from
those runs. Each refuted obligation is itself the error,
`error: verification error: Unsat (thrust: refuted: ...)`, and its last note, naming its part
(`in part 1 of 2, of 2 clauses from ...`), is left out here.

| # | Bug kind | File | Solver | What the report points at | Fix |
|---|---|---|---|---|---|
| 1 | wrong arithmetic | [s01](examples/scenarios/s01_wrong_arith.rs) | z3 | `ensures in withdraw`, `result = -1` | drop `- 1` |
| 2 | caller breaks a precondition, through a helper left to inference | [s02](examples/scenarios/s02_caller_breaks_pre.rs) | z3 | `precondition of withdraw in pay`, run back to `main`'s argument | `pay(80, 50)` |
| 3 | loop bound off by one | [s03](examples/scenarios/s03_loop_off_by_one.rs) | z3 | `ensures in shipping`, one iteration at `n = 0` | `i < n` |
| 4 | bug in a function left to inference | [s04](examples/scenarios/s04_bug_in_inferred_callee.rs) | z3 | `assertion in main`, run through `price.post(units = 10, result = 100)` | `units >= 10` |
| 5 | written invariant not inductive | [s05](examples/scenarios/s05_invariant_not_preserved.rs) | z3 | `loop preservation` (and, split, `ensures`) | `i * (i - 1)` |
| 6 | missing write through `&mut` | [s06](examples/scenarios/s06_missing_write.rs) | z3 | `ensures in swap`, `*old(b) = 1, °old(b) = 1` | add `*b = t` |
| 7 | wrong branch returning `&mut` | [s07](examples/scenarios/s07_wrong_branch_mut.rs) | z3 | `ensures in take_max`, `*a = -1, °a = 2, *b = 0, °b = 0` | `*a >= *b` |
| 8 | contract too weak for a caller | [s08](examples/scenarios/s08_contract_too_weak.rs) | z3 | `assertion in main`, `abs#1 = 6`, assumes the written contract of `abs` | add `ensures(result == x \|\| result == -x)` |
| 9 | impl breaks the trait's contract | [s09](examples/scenarios/s09_impl_breaks_trait.rs) | z3 | `ensures in <Meter as Double>::double`, the trait's `ensures` labelled | `self.m += self.m` |
| 10 | law not provable at an impl | [s10](examples/scenarios/s10_law_fails_at_impl.rs) | PCSat | no refutation; the error at `<Clicks as Counter>::count_nonneg` | model and `count` over `UInt` |
| 11 | wrong assertion in a `for` over a range | [s11](examples/scenarios/s11_for_range_bound.rs) | PCSat | no refutation; the error at `last_index`, part of `last_index`, `main` | `assert!(i < n)` |
| 12 | invariant not found in time | [s12](examples/scenarios/s12_timeout_needs_invariant.rs) | PCSat | `Timeout(60s)` at `sum_capped` | write the `for` invariant |

## 1. Wrong arithmetic

`withdraw` returns `balance - amount - 1` against `ensures(result == balance - amount)`.

```
error: verification error: Unsat (thrust: refuted: ensures in `withdraw`)
 --> s01_wrong_arith.rs:5:2
  |
2 | #[thrust_macros::ensures(result == balance - amount)]
  |                          -------------------------- the annotation it checks
...
  = note: c0: (result = __tmp_mir_withdraw_3 - 1 ∧ __tmp_mir_withdraw_3 = balance - amount ∧ withdraw.bb0(balance, amount, old(balance) = balance, old(amount) = amount)) ==> result = balance - amount
  = note: where it fails: result = -1, balance = 0, amount = 0, __tmp_mir_withdraw_3 = 0
```

## 2. A caller breaks a precondition through a helper

`pay(balance, bill)` has no contract and calls `withdraw(balance, bill)`; `main` calls
`pay(50, 80)`. The failure is reported in `pay`, with `withdraw`'s `requires` labelled, and the
run shows where the values come from.

```
error: verification error: Unsat (thrust: refuted: precondition of `withdraw` in `pay`)
 --> s02_caller_breaks_pre.rs:8:5
  |
1 | #[thrust_macros::requires(amount <= balance)]
  |                           ----------------- the annotation it checks
...
8 |     withdraw(balance, bill)
  |     ^^^^^^^^^^^^^^^^^^^^^^^
  |
  = note: c2: pay.bb0(balance, bill, old(balance) = balance, old(bill) = bill) ==> bill <= balance
  = note: where it fails: balance = 50, bill = 80
  = note: how the solver reaches it: ...
            pay.bb0(balance = 50, bill = 80, old(balance) = 50, old(bill) = 80)   [c5 function entry, s02_caller_breaks_pre.rs:7:1]
              pay.pre(balance = 50, bill = 80)   [c6 argument of `pay`, s02_caller_breaks_pre.rs:12:16]
```

Which side to change (the call, or `pay`'s missing precondition) is the program's intent.

## 3. Loop bound off by one

`while i <= n` in a loop that should run `n` times.

```
error: verification error: Unsat (thrust: refuted: ensures in `shipping`)
   = note: c1: (shipping.loop#1(n, i, cost, old(n) = n) ∧ i > n) ==> cost = 3 * n
   = note: where it fails: cost = 3, n = 0, i = 1
   = note: how the solver reaches it: ...
             shipping.loop#1(n = 0, i = 1, cost = 3, old(n) = 0)   [c2 loop preservation, s03_loop_off_by_one.rs:6:5]
               shipping.loop#1(n = 0, i = 0, cost = 0, old(n) = 0)   [c0 loop entry, s03_loop_off_by_one.rs:6:5]
                 shipping.bb0(n = 0, old(n) = 0)   [c3 function entry, s03_loop_off_by_one.rs:3:1]
```

## 4. Bug in a function left to inference

`price` (no contract) tests `units > 10` for `>= 10`; `main` asserts `price(10) == 90`.

```
error: verification error: Unsat (thrust: refuted: assertion in `main`)
   = note: c7: main.price#1(p) ==> p = 90
   = note: where it fails: p = 100
   = note: how the solver reaches it: ...
             main.price#1(p = 100)   [c5 after call to `price`, s04_bug_in_inferred_callee.rs:10:13]
               price.post(units = 10, result = 100)   [c2 return value, s04_bug_in_inferred_callee.rs:7:2]
                 price.bb3(result = 100, units = 10)   [c0 jump to bb3, s04_bug_in_inferred_callee.rs:2:5]
                   price.bb0(units = 10, old(units) = 10)   [c3 function entry, s04_bug_in_inferred_callee.rs:1:1]
                     price.pre(units = 10)   [c4 argument of `price`, s04_bug_in_inferred_callee.rs:10:13]
   = note: it goes through the contract inferred for `price`: a wrong result there shows here
```

## 5. Written invariant not inductive

`invariant!(.. 2 * s == i * (i + 1))` for `i * (i - 1)`. The whole query shows the
`loop preservation` failure ([chapter 3](03-loops.md)). Split, the written invariant cuts
`sum_below` into three parts, and two fail: the `ensures` is refuted too, with the invariant's
variables shown as `__tmp_chc_c1_4` and `__tmp_chc_c1_2`, and a note says why one function is in
several parts.

```
error: verification error: Unsat (thrust: refuted: ensures in `sum_below`)
...
   = note: c1: (__tmp_chc_c1_4 = __tmp_chc_c1_2 ∧ 0 <= __tmp_chc_c1_4 ∧ 2 * result = __tmp_chc_c1_4 * (__tmp_chc_c1_4 + 1)) ==> 2 * result = __tmp_chc_c1_2 * (__tmp_chc_c1_2 - 1)
   = note: where it fails: result = 1
   = note: in part 2 of 4, of 1 clause from `sum_below` (s05_invariant_not_preserved.rs:13)
error: verification error: Unsat (thrust: refuted: loop preservation in `sum_below`)
...
   = note: where it fails: n = 1, __tmp_mir_sum_below_7 = 0, *__tmp_mir_sum_below_8 = 0, s = 0, i = 1
   = note: in part 3 of 4, of 1 clause from `sum_below` (s05_invariant_not_preserved.rs:6-11)
note: thrust: 4 parts solved on their own, 0 of them from earlier runs
note: thrust: a function can be in several parts: `sum_below` in 3. Its clauses fall apart where they share no unknown, as on the two sides of a written annotation (a contract, an `invariant!`, a refined type), and a clause with no unknown is a part of its own
```

## 6. Missing write through `&mut`

`swap` without `*b = t`; `ensures(!a == *b && !b == *a)`. rustc's warning that `t` is unused
points at the same line.

```
error: verification error: Unsat (thrust: refuted: ensures in `swap`)
  = note: c0: (t = *__tmp_mir_swap_5 ∧ swap.bb0(*a = *__tmp_mir_swap_5, °a = __tmp_mir_swap_4, *b = __tmp_mir_swap_4, °b = __tmp_mir_swap_4, old(a), old(b))) ==> (°old(a) = *old(b) ∧ °old(b) = *old(a))
  = note: where it fails: t = 0, __tmp_mir_swap_4 = 1, *__tmp_mir_swap_5 = 0, *old(a) = 0, °old(a) = 1, *old(b) = 1, °old(b) = 1, result = ()
```

## 7. Wrong branch returning `&mut`

`take_max` with `if *a <= *b { a } else { b }` against the contract of
[chapter 4](04-mutable-references.md). Both `ensures` are labelled as clauses of the annotation:
the refutation does not say which one fails.

```
error: verification error: Unsat (thrust: refuted: ensures in `take_max`)
 --> s07_wrong_branch_mut.rs:9:2
  |
1 | #[thrust_macros::ensures(*a >= *b ==> (*result == *a && !result == !a && !b == *b))]
  |                          -------------------------------------------------------- a clause of the annotation it checks
2 | #[thrust_macros::ensures(*a < *b ==> (*result == *b && !result == !b && !a == *a))]
  |                          ------------------------------------------------------- a clause of the annotation it checks
...
  = note: where it fails: °__tmp_mir_take_max_3 = 2, *__tmp_mir_take_max_7 = -1, *a = -1, °a = 2, *b = 0, °b = 0
```

`*a = -1 < *b = 0`, yet the result is `a` (its current value `*__tmp_mir_take_max_7 = -1`).

## 8. Contract too weak for a caller

`abs` ensures only `result >= 0`; `main` asserts `abs(-5) == 5`. The code is right; the
contract does not say enough, and the solver picks any non-negative result. The last note names
the written contract the run assumes.

```
error: verification error: Unsat (thrust: refuted: assertion in `main`)
   = note: c6: main.abs#1(abs#1) ==> abs#1 = 5
   = note: where it fails: abs#1 = 6
   = note: how the solver reaches it: ...
             main.abs#1(abs#1 = 6)   [c4 after call to `abs`, s08_contract_too_weak.rs:11:13]
   = note: it assumes the written contract of `abs` (s08_contract_too_weak.rs:1:26): a wrong `ensures` there shows here
```

## 9. An impl breaks the trait's contract

`Meter::double` adds 2 instead of doubling (the trait of [chapter 5](05-traits-and-generics.md)).
The label is on the trait's `ensures`, which the impl is checked against.

```
error: verification error: Unsat (thrust: refuted: ensures in `<Meter as Double>::double`)
  --> s09_impl_breaks_trait.rs:28:6
   |
15 |     #[thrust_macros::ensures(Self::is_double(*self, !self))]
   |                              --------------- the annotation it checks
...
   = note: c0: (<Meter as Double>::double.bb0(*self = (*__tmp_mir_Meter_as_Double_double_2, ), °self, old(self)) ∧ (*self).0 = *__tmp_mir_Meter_as_Double_double_2 + 2 ∧ °self = ((*self).0, )) ==> <Meter as Double>::is_double *old(self) °old(self)
   = note: where it fails: °self = (3, ), *__tmp_mir_Meter_as_Double_double_2 = 1, *old(self) = (1, ), °old(self) = (3, ), (*self).0 = 3, result = ()
```

## 10. A law not provable at an impl

The `Counter` of [chapter 5](05-traits-and-generics.md) with `count` returning `Int` over a model
`(Int,)`: the law `count(*c) >= 0` has nothing to stand on. PCSat only (z3 cannot read the query),
so there is no refutation; the error is at the law's impl, and the part names it.

```
note: thrust: no failing obligation to show: the solver gave no refutation (only `z3` is asked for one)

error: verification error: Unsat
  --> s10_law_fails_at_impl.rs:40:5
   |
40 |     fn count_nonneg(c: &Clicks) {}
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: in part 2 of 4, of 2 clauses from `<Clicks as Counter>::count_nonneg` (s10_law_fails_at_impl.rs:40)
```

With `THRUST_REPORT=failure,constraints THRUST_REPORT_ONLY='Clicks::count_nonneg'` the same run
shows the obligation ([chapter 7](07-reading-a-failure.md)).

## 11. A wrong assertion in a `for` over a range

`for i in 0..n { assert!(i < n - 1); .. }`. PCSat only. The error is at the first function of the
part, and the other function of the part is labelled.

```
note: thrust: no failing obligation to show: the solver gave no refutation (only `z3` is asked for one)

error: verification error: Unsat
  --> s11_for_range_bound.rs:1:1
   |
 1 | / fn last_index(n: i64) -> i64 {
...
 8 | | }
   | |_^
 9 |
10 | / fn main() {
11 | |     let _ = last_index(3);
12 | | }
   | |_- `main` is in this part too
   |
   = note: in part 1 of 1, of 14 clauses from `last_index` (s11_for_range_bound.rs:1-8), `main` (s11_for_range_bound.rs:10-12)
```

## 12. An invariant not found in time

`sum_capped` of [chapter 6](06-iterators.md) without its invariant.

```
error: verification error: Timeout(60s)
  --> s12_timeout_needs_invariant.rs:2:1
   |
 2 | / fn sum_capped(v: &Vec<i64>) -> i64 {
...
   = note: in part 1 of 2, of 11 clauses from `sum_capped` (s12_timeout_needs_invariant.rs:2-12)
```

A timeout is not a failure: the fix adds the invariant, not a code change.
