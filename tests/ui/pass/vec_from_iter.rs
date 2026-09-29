//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:0360cb142

fn collect<I: IntoIterator<Item = i64>>(iter: I) -> Vec<i64> {
    Vec::from_iter(iter)
}

fn main() {
    let v = collect(Vec::new());
    assert!(v.len() >= 0);
}
