//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An element of a boxed slice is read and written through the slice the box holds.
#[thrust_macros::requires(i < a.len() && 0 < a.len())]
#[thrust_macros::ensures(result == a[0] + a[i])]
fn read_at(a: Box<[i64]>, i: usize) -> i64 {
    a[0] + a[i]
}

#[thrust_macros::requires(i <= a.len() && 0 < a.len())]
#[thrust_macros::ensures(result[i] == v && result.len() == a.len())]
fn write_at(mut a: Box<[i64]>, i: usize, v: i64) -> Box<[i64]> {
    a[0] = 0;
    a[i] = v;
    a
}

fn main() {}
