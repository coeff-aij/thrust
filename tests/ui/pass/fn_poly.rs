//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:0360cb142

fn left<T, U>(x: (T, U)) -> T {
    x.0
}

fn main() {
    assert!(left((42, 0)) == 42);
}
