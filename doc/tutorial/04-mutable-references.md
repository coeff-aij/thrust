# 4. Mutable references

Thrust models a mutable reference `r: &mut T` by two values: `*r`, what it points to now, and
`!r`, what it will point to when the borrow ends (its final value, a *prophecy*). A function
taking `&mut` states its effect as a relation between the two, and the caller learns the new value
of the borrowed variable from the final value. No ownership or aliasing predicates are written:
the borrow checker already guarantees them. All examples here run with z3.

[examples/04_add_to.rs](examples/04_add_to.rs):

```rust
#[thrust_macros::ensures(!r == *r + a)]
fn add_to(r: &mut i64, a: i64) {
    *r += a;
}

fn main() {
    let mut x = 1;
    add_to(&mut x, 2);
    assert!(x == 3);
}
```

```console
$ thrust 04_add_to.rs; echo "exit $?"
exit 0
```

In a contract `!r` is the final value (`!` on a `&mut` is not negation), and `*r` in `ensures`
is still the value at the call. The same relation can be written
`r == thrust_models::model::Mut::new(*r, *r + a)`.

## A reference returned

The classic example ([examples/04_take_max.rs](examples/04_take_max.rs)): `take_max` returns one
of two references, the caller writes through it, and the assertion depends on which one was
returned.

```rust
fn take_max<'a>(a: &'a mut i64, b: &'a mut i64) -> &'a mut i64 {
    if *a >= *b {
        a
    } else {
        b
    }
}

fn main() {
    let mut a = rand();
    let mut b = rand();
    let m = take_max(&mut a, &mut b);
    *m += 1;
    assert!(a != b);
}
```

Left to inference, the contract of `take_max` comes back in the report, where `°a` is the final
value of `a`:

```console
$ THRUST_REPORT=1 thrust 04_take_max.rs
note: thrust: `take_max`
 --> 04_take_max.rs:7:1
  |
7 | fn take_max<'a>(a: &'a mut i64, b: &'a mut i64) -> &'a mut i64 {
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  |
  = note: contract (inferred)
          inferred: fn take_max(a: mut int, b: mut int) -> {mut int | (*a = *result ∧ °a = °result ∧ *a >= °b ∧ °b = *b) ∨ (*result = *b ∧ °result = °b ∧ *a = °a ∧ *a < *result)}
```

Either the result is `a` (`*result = *a`, `°result = °a`), `b` is left unchanged (`°b = *b`) and
`*a >= *b`; or the result is `b`, `a` is unchanged and `*a < *b` (`*a < *result`). Written as a contract
([examples/04_take_max_contract.rs](examples/04_take_max_contract.rs)):

```rust
#[thrust_macros::ensures(*a >= *b ==> (*result == *a && !result == !a && !b == *b))]
#[thrust_macros::ensures(*a < *b ==> (*result == *b && !result == !b && !a == *a))]
fn take_max<'a>(a: &'a mut i64, b: &'a mut i64) -> &'a mut i64 {
```

```console
$ thrust 04_take_max_contract.rs; echo "exit $?"
exit 0
```

`!result == !a` says that whatever is written through the result ends up in `a`.

## A missing write

[scenarios/s06_missing_write.rs](examples/scenarios/s06_missing_write.rs) is a `swap` that
forgets `*b = t`:

```console
$ THRUST_REPORT=1 thrust s06_missing_write.rs
warning: unused variable: `t`
 --> s06_missing_write.rs:3:9
  |
3 |     let t = *a;
  |         ^ help: if this is intentional, prefix it with an underscore: `_t`
  |
  = note: `#[warn(unused_variables)]` (part of `#[warn(unused)]`) on by default

error: verification error: Unsat (thrust: refuted: ensures in `swap`)
 --> s06_missing_write.rs:2:1
  |
1 | #[thrust_macros::ensures(!a == *b && !b == *a)]
  |                          -------------------- the annotation it checks
2 | fn swap(a: &mut i64, b: &mut i64) {
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  |
  = note: c0: (t = *__tmp_mir_swap_5 ∧ swap.bb0(*a := *__tmp_mir_swap_5, °a := __tmp_mir_swap_4, *b := __tmp_mir_swap_4, °b := __tmp_mir_swap_4, *old(a), °old(a), *old(b), °old(b))) ==> (°old(a) = *old(b) ∧ °old(b) = *old(a))
  = note: where it fails: t = 0, __tmp_mir_swap_4 = 1, *__tmp_mir_swap_5 = 0, *old(a) = 0, °old(a) = 1, *old(b) = 1, °old(b) = 1, result = ()
  = note: how the solver reaches it: each fact follows, by the constraint in brackets, from the facts indented under it (a derivation, not an order of execution):
            swap.bb0(*a = 0, °a = 1, *b = 1, °b = 1, *old(a) = 0, °old(a) = 1, *old(b) = 1, °old(b) = 1)   [c1 function entry, s06_missing_write.rs:2:1]
  = note: the solver refutes one obligation of a query: others may fail too (`THRUST_SPLIT` refutes one in each part)

error: aborting due to 1 previous error; 1 warning emitted
```

The values give each reference its current and final value: `*old(b) = 1, °old(b) = 1` says `b`
pointed to 1 and still does at the end, while the contract asks for `°b = *a = 0`. In the
constraint, a reference passed to an unknown is given by its two values (`*b := ...`,
`°b := ...`), and one that is the template's own variable by its two names (`*old(a), °old(a)`).
rustc's warning that `t` is unused points at the same bug.

Mutable references inside data (`Option<&mut T>`, a `Vec` of them, a struct field) follow the same
model; see [Mutable references](../../README.md#mutable-references) for the notation.
