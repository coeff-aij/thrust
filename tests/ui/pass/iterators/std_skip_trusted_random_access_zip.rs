//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// `Zip` over `TrustedRandomAccess` iterators reads their sizes, 0 for the `Skip` here, and takes
// nothing from either: the closure, which never returns on 0, is not run.
fn main() {
    let f = thrust_macros::closure!(
        requires(true),
        ensures(x != 0 && result == x),
        |x: i64| -> i64 { if x == 0 { loop {} } x },
    );
    let mut z = std::iter::zip((0..1i64).map(f).skip(5), 0..3i64);
    match z.next() {
        None => {}
        Some(_) => assert!(false),
    }
}
