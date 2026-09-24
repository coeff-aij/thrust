//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// A concrete call reaches a generic function through an intermediate generic
// function that passes its own type parameter on.

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn mk<T>() -> T {
    unimplemented!()
}

fn five<T>(_t: T) -> i64 {
    5
}

fn outer<T>() -> i64 {
    five(mk::<T>())
}

fn main() {
    assert!(outer::<i64>() == 6);
}
