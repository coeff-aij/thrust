//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `take(5)` over a range of two items hands out both and then completes.

fn main() {
    assert!((0..2).take(5).count() == 2);
}
