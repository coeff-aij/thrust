//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

fn collect<I: IntoIterator<Item = i64>>(iter: I) -> Vec<i64> {
    Vec::from_iter(iter)
}

fn main() {
    let v = collect(Vec::new());
    assert!(v.len() >= 0);
}
