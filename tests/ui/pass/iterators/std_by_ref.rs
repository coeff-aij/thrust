//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `by_ref` lends the iterator: `take` and `count` step the `&mut Range` it returns.

fn main() {
    let mut it = 0..10;
    assert!(it.by_ref().take(2).count() == 2);
}
