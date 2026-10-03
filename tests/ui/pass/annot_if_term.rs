//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::model::{Array, Int};
use thrust_models::forall;

// An `if` whose branches are terms is the term `ite(cond, then, else)`.

#[thrust_macros::ensures(forall(|i: Int| !(0 <= i) || Array::<Int, Int>::from_fn(|j: Int| if j < n { j } else { n })[i] <= n))]
fn clamp(n: i64) {}

fn main() {}
