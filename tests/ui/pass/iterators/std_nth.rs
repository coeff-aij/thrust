//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `nth` hands out the item after `n` others and leaves the iterator after it.

fn main() {
    let mut r = 0..10;
    assert!(matches!(r.nth(3), Some(3)));
    assert!(matches!(r.next(), Some(4)));
}
