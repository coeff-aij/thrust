//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `Option`'s order puts `None` below every `Some`.

fn main() {
    let a: Option<u64> = Some(3);
    let b: Option<u64> = None;
    assert!(a.max(b) == Some(3));
}
