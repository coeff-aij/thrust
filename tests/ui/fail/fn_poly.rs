//@error-in-other-file: Unsat
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

fn left<T, U>(x: (T, U)) -> T {
    x.0
}

fn main() {
    assert!(left((42, 0)) == 0);
}
