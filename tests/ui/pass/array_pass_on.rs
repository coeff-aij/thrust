//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An array reached through two references, the first element of a slice of arrays, and the
// payload of an `Option` passed on to a callee: the callee's parameter type fixes the length.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn by_ref(x: &[i64; 2]) -> i64 {
    x[0]
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn by_value(x: [i64; 2]) -> i64 {
    x[1]
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn through_two_refs(r: &&[i64; 2]) -> i64 {
    by_ref(*r)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn first_of_slice(v: &[[i64; 2]]) -> i64 {
    match v.first() {
        Some(x) => by_ref(x),
        None => 0,
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn option_payload(o: Option<[i64; 2]>) -> i64 {
    match o {
        Some(a) => by_value(a),
        None => 0,
    }
}

fn main() {}
