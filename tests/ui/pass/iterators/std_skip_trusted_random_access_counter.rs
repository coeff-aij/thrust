//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// `Zip` over `TrustedRandomAccess` iterators reads their sizes, 0 for the `Skip` here, and takes
// nothing from either: the closure, which counts its calls, is not run on the item the `Skip`
// would drop.
fn main() {
    let mut calls = 0i64;
    {
        let c = &mut calls;
        let f = thrust_macros::closure!(
            captures(c: &mut &mut i64),
            requires(true),
            ensures(*!c == **c + 1 && result == x),
            move |x: i64| -> i64 { *c += 1; x },
        );
        let mut z = std::iter::zip((0..1i64).map(f).skip(1), 0..3i64);
        assert!(z.next().is_none());
    }
    assert!(calls == 0);
}
