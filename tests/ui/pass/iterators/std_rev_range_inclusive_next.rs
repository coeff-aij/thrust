//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `(0..=3).rev()` hands out the range's end first.

fn main() {
    let mut r = (0..=3).rev();
    assert!(matches!(r.next(), Some(3)));
}
