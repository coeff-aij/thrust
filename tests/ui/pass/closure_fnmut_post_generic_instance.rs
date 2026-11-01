//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
use thrust_models::{forall, model::Closure};

// A generic function states `post!` of the `FnMut` state it takes by value: a call that ends in
// some state and drops it, so the borrow the closure captures ends at the value that call left.
// Its body makes that one call and drops `f`.
#[thrust_macros::requires(forall(|c: Closure<F>| thrust_macros::pre!(c())))]
#[thrust_macros::ensures(thrust_macros::hist_inv!(f, f))]
#[thrust_macros::ensures(thrust_macros::post!(f(), result))]
fn call<F: FnMut() -> i64>(mut f: F) -> i64 {
    f()
}

fn main() {
    let mut n: i64 = 0;
    let c = thrust_macros::closure!(
        captures(n: &mut &mut i64),
        requires(true),
        ensures(*(!n) == *(*n) + 1 && result == *(*n) + 1),
        ensures(!(!n) == !(*n)),
        || -> i64 {
            n += 1;
            n
        },
    );
    let r = call(c);
    assert!(r == 1);
    assert!(n == 1);
}
