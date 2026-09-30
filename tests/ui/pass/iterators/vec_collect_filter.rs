//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:9799dfd7b

fn main() {
    let mut xs: Vec<i64> = Vec::new();
    xs.push(1);
    xs.push(2);
    let v: Vec<i64> = xs.into_iter().filter(|x| 100 / (100 - *x) > 0).collect();
}
