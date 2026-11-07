//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// The in-place `collect` into a `Vec` over a `TrustedRandomAccess` iterator reads its size, 0 for
// the `Skip` here, and takes nothing from it: the closure, which never returns on 0, is not run.
fn main() {
    let f = thrust_macros::closure!(
        requires(true),
        ensures(x != 0 && result == x),
        |x: i64| -> i64 { if x == 0 { loop {} } x },
    );
    let mut v: Vec<i64> = Vec::new();
    v.push(0);
    let w: Vec<i64> = v.into_iter().map(f).skip(5).collect();
    assert!(w.len() == 0);
}
