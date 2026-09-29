//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:0360cb142

fn lt<T>(x: &T, y: &T) -> bool where T: Ord + PartialOrdSpec {
    x < y
}

fn main() {
    assert!(lt(&1, &2));
}
