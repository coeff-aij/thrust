//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An array passed by value or by reference has the length its type fixes, so a bound on the
// index alone shows it in bounds.
#[thrust_macros::requires(i < 2)]
fn sum_at(a: [i64; 2], b: [i64; 2], i: usize) -> i64 {
    a[i] + b[i]
}

#[thrust_macros::requires(i < 3)]
#[thrust_macros::ensures(result[i] == v)]
fn set_at(mut a: [i64; 3], i: usize, v: i64) -> [i64; 3] {
    a[2] = 0;
    a[i] = v;
    a
}

#[thrust_macros::requires(i < 2)]
fn first_and(a: &[i64; 2], i: usize) -> i64 {
    a[0] + a[i]
}

#[thrust_macros::requires(i < 2)]
fn write_through(a: &mut [i64; 2], i: usize, v: i64) {
    a[i] = v;
}

fn main() {}
