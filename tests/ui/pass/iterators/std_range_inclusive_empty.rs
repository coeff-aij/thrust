//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An inclusive range whose start passes its end has no items.

fn main() {
    assert!((3..=2).count() == 0);
}
