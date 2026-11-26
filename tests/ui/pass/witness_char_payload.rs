//@check-pass
//@compile-flags: -Adead_code -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::exists;
use thrust_models::Ghost;

#[thrust_macros::predicate]
fn some_max(n: i64) -> bool {
    exists(|o: Option<char>| n == 0 && o == Some(char::MAX))
}

// The variable of an `exists` at an enum holding a `char` is its one variable: `witness` takes one
// term for it, and `choose!` names one value of it, whose payload has the facts of a `char`.

#[thrust_macros::requires(n == 0)]
#[thrust_macros::ensures(some_max(n))]
fn by_witness(n: i64) {
    thrust_macros::proof_assert!(|n: i64| thrust_models::witness(some_max(n), Some(char::MAX)));
}

#[thrust_macros::requires(some_max(n))]
#[thrust_macros::ensures(true)]
fn by_choose(n: i64) {
    let o = thrust_macros::choose!(|n: i64| -> Option<char> { some_max(n) });
    thrust_macros::proof_assert!(|o: Ghost<Option<char>>| o == Some(char::MAX));
}

fn main() {
    by_witness(0);
    by_choose(0);
}
