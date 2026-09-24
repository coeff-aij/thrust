//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x)]
fn id<T>(x: T) -> T {
    x
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x)]
fn apply_twice<T>(x: T) -> T {
    id(id(x))
}

fn main() {
    assert!(apply_twice(42) == 42);
}
