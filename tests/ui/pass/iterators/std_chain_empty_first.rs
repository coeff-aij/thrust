//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `chain` whose first iterator is empty hands out the second's items from the start.

fn main() {
    let v: Vec<i64> = (0..0).chain(5..7).collect();
    assert!(v.len() == 2 && v[0] == 5);
}
