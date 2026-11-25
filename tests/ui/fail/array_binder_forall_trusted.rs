//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A binder of an array type does not range over arrays of other lengths: a trusted `forall`
// that holds of every `[i64; 2]` says nothing of the length of `v`.
use thrust_models::forall;

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(forall(|a: [i64; 2]| a.len() == 2))]
fn arrays_have_len_two() {
    unimplemented!()
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn read(v: &[i64]) -> i64 {
    arrays_have_len_two();
    v[5]
}

fn main() {}
