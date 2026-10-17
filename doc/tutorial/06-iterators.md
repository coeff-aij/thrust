# 6. Iterators and `for`

A `for` loop calls `Iterator::next` until it returns `None`. Thrust verifies it through the
specifications `std.rs` gives the standard iterators: a type implementing the spec trait
`IteratorSpec` has two predicates, `produces(self, visited, o)` (stepping from `self` to `o`
returns the items `visited`) and `completed(self)`, and `next`'s contract is stated with them.
`std.rs` implements it for integer ranges, slice and `Vec` iterators, and adapters such as
`Enumerate` and `Zip`. All examples here need PCSat:

```sh
export THRUST_SOLVER=$THRUST/tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
```

## Inferred

[examples/06_for_range.rs](examples/06_for_range.rs):

```rust
fn count(n: i64) -> i64 {
    let mut c = 0;
    for i in 0..n {
        assert!(i < n);
        c += 1;
    }
    c
}

fn main() {
    let _ = count(3);
}
```

```console
$ thrust 06_for_range.rs; echo "exit $?"
exit 0
```

Over a slice ([examples/06_for_slice_inferred.rs](examples/06_for_slice_inferred.rs)):

```rust
#[thrust_macros::ensures(result <= v.len())]
fn count_pos(v: &Vec<i64>) -> usize {
    let mut c = 0;
    for x in v.iter() {
        if *x > 0 {
            c += 1;
        }
    }
    c
}
```

This verifies too, but took PCSat about 18 s.

## Writing the invariant of a `for`

In a function under `#[thrust_macros::context]`, an invariant at the start of a `for` body may
name the iterator `iter`, the iterator before the loop `iter_old`, and `produced`, the ghost
sequence of the items returned so far. Thrust then conjoins `produces(iter_old, produced, iter)`
to it. [examples/06_for_slice.rs](examples/06_for_slice.rs) is `count_pos` with one:

```rust
use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::context]
#[thrust_macros::ensures(result <= v.len())]
fn count_pos(v: &Vec<i64>) -> usize {
    let mut c = 0;
    for x in v.iter() {
        thrust_macros::invariant!(|iter: core::slice::Iter<'_, i64>,
                                   iter_old: Ghost<core::slice::Iter<'_, i64>>,
                                   produced: Ghost<Seq<Int>>,
                                   c: usize,
                                   v: thrust_models::FnParam<&Vec<i64>>|
            iter_old.0 == *v.at_entry() && iter_old.1 == 0 && c <= produced.len());
        if *x > 0 {
            c += 1;
        }
    }
    c
}
```

It verifies in about a second. A slice iterator's model is the pair (the sequence, the cursor), so
`iter_old.0 == *v.at_entry() && iter_old.1 == 0` says the loop started at the beginning of `v`.

Sometimes the invariant is not found in time. [examples/06_sum_slice.rs](examples/06_sum_slice.rs):

```rust
#[thrust_macros::ensures(result <= 100 * v.len())]
fn sum_capped(v: &Vec<i64>) -> i64 {
    let mut s = 0;
    for x in v.iter() {
        if *x <= 100 {
            s += *x;
        } else {
            s += 100;
        }
    }
    s
}
```

```console
$ thrust 06_sum_slice.rs
...
error: verification error: Timeout(60s)

error: aborting due to 1 previous error; 1 warning emitted
```

With the invariant `iter_old.0 == *v.at_entry() && iter_old.1 == 0 && s <= 100 * produced.len()`
([examples/06_sum_slice_invariant.rs](examples/06_sum_slice_invariant.rs)) it verifies in about a
second.

The iterators with an `IteratorSpec` impl in [std.rs](../../std.rs) are `Range` of the integer
types, `slice::Iter`, `vec::IntoIter`, `Enumerate` and `Zip` of them; `slice::IterMut` has its own
`next` contract. A `for` over another iterator (`map`, `filter`, `rev`, a `RangeInclusive`) has no
contract here. The rules for `iter`, `iter_old` and `produced` are in the README's paragraph on
`for` loops under [Loop invariants](../../README.md#loop-invariants).
