//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=all

// A narrowing `as` gives its result the target type, so `y + 1` is checked against the range of
// `i32`: it overflows at `x == i32::MAX`.

#[thrust::callable]
fn f(x: i64) {
    let y = x as i32;
    let z = y + 1;
    assert!(z > y);
}

fn main() {}
