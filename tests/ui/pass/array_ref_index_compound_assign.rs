//@check-pass
//@compile-flags: -C overflow-checks=on -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn main() {
    let mut a = [1i64, 2, 3];
    let r = &mut a;
    let i = 1;
    r[i] += 1;
    assert!(a[0] == 1);
    assert!(a[1] == 3);
    assert!(a[2] == 3);
}
