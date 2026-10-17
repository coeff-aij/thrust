//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `Vec::extend` appends what the iterator produced up to its completion.

fn main() {
    let mut v: Vec<i64> = Vec::new();
    v.push(7);
    v.extend(0..3);
    assert!(v.len() == 4);
    assert!(v[0] == 7 && v[3] == 2);
}
