//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:9799dfd7b

fn main() {
    let mut xs: Vec<i64> = Vec::new();
    xs.push(1);
    xs.push(2);
    let mut v: Vec<i64> = Vec::new();
    v.extend(xs.iter().map(|x| {
        assert!(*x < 100);
        *x * 10
    }));
}
