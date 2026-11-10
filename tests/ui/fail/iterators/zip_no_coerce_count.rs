//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// Over two `TrustedRandomAccessNoCoerce` iterators, std's `Zip::fold`, which `count` runs, hands out
// as many items as the smaller size, 0 here, by index and does not call `next` (`ZipImpl` in
// core/src/iter/adapters/zip.rs): the closure, which never returns on 0, is not run on the
// `Vec`'s item. `next` would run it: `vec::IntoIter` is not `TrustedRandomAccess`.
fn main() {
    let f = thrust_macros::closure!(
        requires(true),
        ensures(x != 0 && result == x),
        |x: i64| -> i64 { if x == 0 { loop {} } x },
    );
    let mut v: Vec<i64> = Vec::new();
    v.push(0);
    let n = std::iter::zip(v.into_iter().map(f), 0..0i64).count();
    assert!(n != 0);
}
