//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::model::{Array, Int};
use thrust_models::forall;

// `Array::from_fn(f)` is the array whose element at each index `i` is `f(i)` (SMT-LIB's `lambda`).

#[thrust_macros::ensures(forall(|i: Int| Array::<Int, Int>::from_fn(|j: Int| j + n)[i] == i + n))]
fn shift(n: i64) {}

fn main() {}
