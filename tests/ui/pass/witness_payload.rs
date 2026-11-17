//@check-pass
//@compile-flags: -Adead_code -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::exists;
use thrust_models::model::Int;

#[thrust_macros::predicate]
fn positive(x: Option<i64>) -> bool {
    exists(|v: Int| x == Some(v) && v > 0)
}

// The `exists` of `positive` binds the payload of `x`, which the stored definition reads through
// a selector; `witness` instantiates the `exists` as written: the goal is `y == Some(3) && 3 > 0`.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(positive(result))]
fn three() -> Option<i64> {
    let y = Some(3);
    thrust_macros::proof_assert!(|y: Option<i64>| thrust_models::witness(positive(y), 3));
    y
}

fn main() {
    three();
}
