//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A binder of an array type ranges over the arrays of that length, as the type's values do.
use thrust_models::{exists, forall};

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(forall(|a: [i64; 2]| a.len() == 2))]
fn all_have_len() {}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(exists(|a: [i64; 2]| a.len() == 2))]
fn some_has_len() {}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(forall(|a: [i64; 2]| a.len() == 2))]
fn arrays_have_len_two() {
    unimplemented!()
}

#[thrust_macros::requires(v.len() > 5)]
#[thrust_macros::ensures(true)]
fn read(v: &[i64]) -> i64 {
    arrays_have_len_two();
    v[5]
}

fn main() {}
