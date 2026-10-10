//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `for` over a range of `i64` with the loop invariant inferred: `into_iter` is the identity
// and `next` is `Iterator::next`'s contract through the range's `IteratorSpec` impl.

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
