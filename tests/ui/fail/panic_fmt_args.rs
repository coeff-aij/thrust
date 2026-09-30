//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744
fn check(x: i64) {
    if x < 0 {
        panic!("x = {}", x);
    }
}

fn main() {
    check(-1);
}
