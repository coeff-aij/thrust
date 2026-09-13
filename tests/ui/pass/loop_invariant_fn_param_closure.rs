//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
use thrust_models::forall;

// A loop invariant refers to a closure parameter via `FnParam<F>`, whose
// `f.at_entry()` yields `Closure<F>`. Here the invariant relates `acc` to the
// entry closure's postcondition, from which the postcondition below is proven.
// The generic `f` needs its precondition assumed to be called at all, the
// invariant needs an explicit upper bound on `i` to conclude `i == n` at loop
// exit, and it must restate that precondition since a hand-written invariant
// replaces the inferred loop predicate rather than extending it.
#[thrust_macros::requires(forall(|x: i64| thrust_macros::pre!(f(x))))]
#[thrust_macros::ensures((n > 0) ==> thrust_macros::post!(f(n - 1), result))]
#[thrust_macros::context]
fn last_apply<F>(f: F, n: i64) -> i64
where
    F: Fn(i64) -> i64,
{
    let mut acc = 0_i64;
    let mut i = 0_i64;
    while i < n {
        thrust_macros::invariant!(
            |i: i64, acc: i64, n: i64, f: thrust_models::FnParam<F>|
            ((n > 0) ==> i <= n)
                && ((i > 0) ==> thrust_macros::post!(f.at_entry()(i - 1), acc))
                && forall(|x: i64| thrust_macros::pre!(f.at_entry()(x)))
        );
        acc = f(i);
        i += 1;
    }
    acc
}

// A capture-free closure is null (singleton) sorted; comparing its identity
// must collapse to a canonical value rather than ICE during clause building.
#[thrust_macros::context]
fn unchanged<F>(mut f: F)
where
    F: FnMut(i64) -> i64,
{
    let _ = &mut f;
    let mut i = 0_i64;
    while i < 10 {
        thrust_macros::invariant!(
            |i: i64, f: thrust_models::FnParam<F>|
            f.at_entry() == f.at_entry() && i <= 10
        );
        i += 1;
    }
    assert!(i == 10);
}

fn main() {
    let c = 7_i64;
    let _ = last_apply(|x| x + c, 10);

    unchanged(|x| x + 1);
}
