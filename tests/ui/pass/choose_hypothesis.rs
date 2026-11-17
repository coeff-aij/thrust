//@check-pass
//@compile-flags: -Adead_code -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::exists;
use thrust_models::Ghost;

#[thrust_macros::predicate]
fn even(n: i64) -> bool {
    exists(|k: i64| n == 2 * k)
}

// `choose!` checks that its formula holds, here the precondition's `even(n)`, and names a witness
// of it: `k` satisfies the body of the `exists` from then on.

#[thrust_macros::requires(even(n) && 0 <= n && n <= 1000)]
#[thrust_macros::ensures(true)]
fn half(n: i64) {
    let k = thrust_macros::choose!(|n: i64| -> i64 { even(n) });
    thrust_macros::proof_assert!(|n: i64, k: Ghost<i64>| n == 2 * k);
}

fn main() {
    half(4);
}
