//@check-pass
//@compile-flags: -C overflow-checks=on -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn main() {
    let mut v = Vec::new();
    v.push(1i64);
    v.push(2);
    v.push(3);
    let i = 1;
    v[i] += 1;
    assert!(v[0] == 1);
    assert!(v[1] == 3);
    assert!(v[2] == 3);
}
