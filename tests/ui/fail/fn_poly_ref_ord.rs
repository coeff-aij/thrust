//@error-in-other-file: Unsat
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn lt<T>(x: &T, y: &T) -> bool where T: Ord + PartialOrdSpec {
    x < y
}

fn main() {
    assert!(lt(&1, &0));
}
