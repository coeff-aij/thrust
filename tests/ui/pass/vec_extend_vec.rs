//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn main() {
    let mut v: Vec<i64> = Vec::new();
    v.extend(Vec::<i64>::new());
    assert!(v.len() >= 0);
}
