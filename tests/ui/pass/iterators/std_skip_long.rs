//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `skip(5)` over a range of two items hands out nothing.

fn main() {
    assert!((0..2).skip(5).count() == 0);
}
