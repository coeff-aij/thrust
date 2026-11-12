//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::exists;
use thrust_models::Ghost;

#[thrust_macros::predicate]
fn halves(n: i64) -> bool {
    exists(|a: i64, b: i64| n == a + b && a == b)
}

// `choose!` of an `exists` that binds two variables names a tuple of witnesses: `p.0` and `p.1`
// satisfy the body from then on. The assertion is false: `p.0` is half of `n`, not `n`.

#[thrust_macros::requires(halves(n) && 0 <= n && n <= 1000)]
#[thrust_macros::ensures(true)]
fn half(n: i64) {
    let p = thrust_macros::choose!(|n: i64| -> (i64, i64) { halves(n) });
    thrust_macros::proof_assert!(|n: i64, p: Ghost<(i64, i64)>| n == p.0);
}

fn main() {
    half(4);
}
