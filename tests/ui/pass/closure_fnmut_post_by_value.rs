//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// Trusted functions state `post!` of a closure they take by value, at an `FnMut` and at an
// `FnOnce` bound, and are given a closure that changes its state. `post!` of a state holds of a
// call from it that ends in some state, so the result is the one the closure returns.
#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(f()))]
#[thrust_macros::ensures(thrust_macros::post!(f(), result))]
fn call_mut<F: FnMut() -> i64>(mut f: F) -> i64 { f() }

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(f()))]
#[thrust_macros::ensures(thrust_macros::post!(f(), result))]
fn call_once<F: FnOnce() -> i64>(f: F) -> i64 { f() }

fn main() {
    let mut n: i64 = 0;
    let r = call_mut(move || -> i64 { n += 1; n });
    assert!(r == 1);

    let mut m: i64 = 0;
    let c = move || -> i64 { m += 1; m };
    let s = call_once(c);
    assert!(s == 1);
}
