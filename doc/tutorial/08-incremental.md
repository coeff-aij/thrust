# 8. Verify, fix, verify again

Thrust solves one query for the whole crate by default. Two variables make the loop of verifying,
fixing and verifying again cheaper:

- `THRUST_SPLIT=<n>` solves each part of the constraints on its own, `n` at a time. A part is a
  set of constraints that share an unknown. A function with a written contract shares none with
  its callers, so its body is a part of its own; a function left to inference is in its callers'
  part. The crate verifies exactly when every part does.
- `THRUST_CACHE_DIR=<dir>` keeps the verdict of each part, keyed by the part's query and the
  solver. A part that a change did not touch is not solved again.

With `THRUST_REPORT=1`, each failing part gets its own refutation (chapter 7), and each part that
passes shows what is inferred in it. The details are in
[Solving a crate in parts](../../README.md#solving-a-crate-in-parts).

## A session

The program is `shop.rs` of [chapter 7](07-reading-a-failure.md), with three bugs; each step
copies the next version over it ([examples/08_shop_1.rs](examples/08_shop_1.rs) to
[08_shop_5.rs](examples/08_shop_5.rs)). Solver: z3.

```sh
export THRUST_SPLIT=4 THRUST_CACHE_DIR=.thrust-cache THRUST_REPORT=1
```

Run 1, three bugs: three parts, all solved, all failing.

```console
$ cp 08_shop_1.rs shop.rs; thrust shop.rs
note: thrust: refuted: ensures in `withdraw`
 --> shop.rs:5:2
...
  = note: where it fails: result = -1, balance = 0, amount = 0, __tmp_mir_withdraw_3 = 0
...
note: thrust: refuted: ensures in `shipping`
...
note: thrust: refuted: assertion in `main`
...
error: verification error: Unsat
 --> shop.rs:5:2
  |
5 | }
  |  ^
  |
  = note: in part 0 of 3, of 2 clauses from `withdraw` (shop.rs:3-5)

error: verification error: Unsat
  --> shop.rs:17:2
   |
17 | }
   |  ^
   |
   = note: in part 1 of 3, of 4 clauses from `shipping` (shop.rs:9-17)

error: verification error: Unsat
  --> shop.rs:29:5
   |
29 |     assert!(p == 90);
   |     ^^^^^^^^^^^^^^^^
   |
   = note: in part 2 of 3, of 16 clauses from `price` (shop.rs:19-25), `main` (shop.rs:27-33)

note: thrust: 3 parts solved on their own, 0 of them from earlier runs

error: aborting due to 3 previous errors
```

Run 2, `withdraw` fixed (`balance - amount`): only its part is solved again, and it passes; the
other two come from the cache and still fail. The last note names the parts solved now.

```console
$ cp 08_shop_2.rs shop.rs; thrust shop.rs
note: thrust: refuted: ensures in `shipping`
...
note: thrust: refuted: assertion in `main`
...
error: verification error: Unsat
  --> shop.rs:17:2
...
   = note: in part 1 of 3, of 4 clauses from `shipping` (shop.rs:9-17)

error: verification error: Unsat
  --> shop.rs:29:5
...
   = note: in part 2 of 3, of 16 clauses from `price` (shop.rs:19-25), `main` (shop.rs:27-33)

note: thrust: 3 parts solved on their own, 2 of them from earlier runs; solved now: part 0 from `withdraw` (shop.rs:3-5)

error: aborting due to 2 previous errors
```

The same run with `THRUST_REPORT_FORMAT=json THRUST_REPORT_FILE=r2.jsonl` gives the parts as:

```console
$ grep '"kind":"part"' r2.jsonl | jq -c '{id, functions: [.functions[].fn], verdict, cached}'
{"id":0,"functions":["withdraw"],"verdict":"sat","cached":false}
{"id":1,"functions":["shipping"],"verdict":"unsat","cached":true}
{"id":2,"functions":["price","main"],"verdict":"unsat","cached":true}
```

A cached `unsat` is solved once more to get its refutation; only the verdict is cached.

Run 3, loop bound fixed (`i < n`): `shipping`'s part is solved again and passes, so the report
also shows the invariant inferred there, while `main`'s part still fails.

```console
$ cp 08_shop_3.rs shop.rs; thrust shop.rs
note: thrust: refuted: assertion in `main`
  --> shop.rs:29:5
...
   = note: it goes through the contract inferred for `price`: a wrong result there shows here

note: thrust: loop in `shipping`
  --> shop.rs:12:11
   |
12 |     while i < n {
   |           ^^^^^
   |
   = note: invariant (inferred)
           shipping.loop#1(n: int, i: int, cost: int, old(n): int)
           := (3 * i = cost ∧ 3 * old(n) - cost > -1) ∨ (old(n) >= 0 ∧ n = old(n) ∧ i = 0 ∧ cost = 0)

error: verification error: Unsat
  --> shop.rs:29:5
...
   = note: in part 2 of 3, of 16 clauses from `price` (shop.rs:19-25), `main` (shop.rs:27-33)

note: thrust: 3 parts solved on their own, 2 of them from earlier runs; solved now: part 1 from `shipping` (shop.rs:9-17)

error: aborting due to 1 previous error
```

Run 4, `price` fixed (`units >= 10`): the part of `main` and `price` is solved again, and the
crate verifies.

```console
$ cp 08_shop_4.rs shop.rs; thrust shop.rs; echo "exit $?"
note: thrust: loop in `shipping`
...
note: thrust: `price`
...
note: thrust: 3 parts solved on their own, 2 of them from earlier runs; solved now: part 2 from `price` (shop.rs:19-25), `main` (shop.rs:27-33)

exit 0
```

Run 5, a new assertion in `main` (`assert!(shipping(0) == 0)`): only `main`'s part changes. A run
with nothing changed takes every verdict from the cache:

```console
$ cp 08_shop_5.rs shop.rs; thrust shop.rs; echo "exit $?"
...
note: thrust: 3 parts solved on their own, 2 of them from earlier runs; solved now: part 2 from `price` (shop.rs:19-25), `main` (shop.rs:27-34)

exit 0
$ thrust shop.rs; echo "exit $?"
...
note: thrust: 3 parts solved on their own, 3 of them from earlier runs

exit 0
```

Each run here takes under a second; the cache matters when a part takes the solver minutes.

## With PCSat

The same session with PCSat gives the same parts and verdicts, without refutations: each error is
at the code of its part. Set `THRUST_CACHE_SALT` to the image's id, so that a new solver build
does not reuse the old one's verdicts:

```console
$ export THRUST_SOLVER=$THRUST/tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
$ export THRUST_CACHE_SALT=$(docker image inspect --format '{{.Id}}' "$COAR_IMAGE")
$ cp 08_shop_2.rs shop.rs; thrust shop.rs        # after a run on 08_shop_1.rs
note: thrust: no failing obligation to show: the solver gave no refutation (only `z3` is asked for one)

error: verification error: Unsat
  --> shop.rs:9:1
   |
 9 | / fn shipping(n: i64) -> i64 {
10 | |     let mut i = 0;
11 | |     let mut cost = 0;
12 | |     while i <= n {
...  |
16 | |     cost
17 | | }
   | |_^
   |
   = note: in part 1 of 3, of 4 clauses from `shipping` (shop.rs:9-17)

error: verification error: Unsat
  --> shop.rs:19:1
   |
19 | / fn price(units: i64) -> i64 {
...
   = note: in part 2 of 3, of 16 clauses from `price` (shop.rs:19-25), `main` (shop.rs:27-33)

note: thrust: 3 parts solved on their own, 2 of them from earlier runs; solved now: part 0 from `withdraw` (shop.rs:3-5)

error: aborting due to 2 previous errors
```

## What to expect

- Without `THRUST_SPLIT`, one refutation per run; with it, one per failing part.
- The solver's time limit applies to each part. A part can time out alone where the whole query
  does not, and the other way round. A part that times out is an error without a refutation.
- Every part carries the crate's datatypes and definitions, so adding a type or a logic function
  anywhere solves every part again.
- A part that passes is solved once more for its model, so the report shows what is inferred in
  it, as without `THRUST_SPLIT` (run 3 above).
- The clauses of one function can fall into several parts: they are cut where they share no
  unknown, on the two sides of a written contract, `invariant!` or refined type. A note says so
  for the functions of a failing part, as in [scenario 5](scenarios.md):
  `note: thrust: a function can be in several parts: `sum_below` in 3. ...`.
- A function left to inference is in its callers' part, so a bug in it is solved and reported
  with them (`main`, `price` above). Writing its contract gives it a part of its own.

A coding agent can run the same loop on the JSON report: read the verdict line and the `failure`
lines (`obligation`, `span`, `annotation`, `values`, `premises`, `conclusion`, `run`, `part`),
fix, and run again; the `part` lines also show parts that timed out, with the spans of their
functions.
