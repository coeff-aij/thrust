//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// `Take::fold` over a `TrustedRandomAccess` `Skip` reads its size, 0 here, and takes nothing
// from the inner iterator: the closure, which never returns on 0, is not run.
fn main() {
    let f = thrust_macros::closure!(
        requires(true),
        ensures(x != 0 && result == x),
        |x: i64| -> i64 { if x == 0 { loop {} } x },
    );
    let n = (0..1i64).map(f).skip(5).take(3).count();
    assert!(n == 0);
}
