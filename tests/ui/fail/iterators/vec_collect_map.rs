//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:9799dfd7b

fn main() {
    let mut xs: Vec<i64> = Vec::new();
    xs.push(1);
    xs.push(200);
    let v: Vec<i64> = xs.iter().map(thrust_macros::closure!(
        requires(*x < 100),
        ensures(result == *x * 10),
        |x: &i64| -> i64 { *x * 10 }
    )).collect();
}
