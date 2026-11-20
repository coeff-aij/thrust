//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -A unused-variables -A unused-braces -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
//@require-annotations-for-level: WARN

use thrust_models::{exists, witness};

// A `witness` whose term is not used is warned about: anywhere but a conjunct of a
// `proof_assert!`, `block_ensures!` or `choose!`. A conjunct of a `proof_assert!` and a `choose!`
// (which expands to a `witness`) are not; the conjunct's term is checked, and its wrong witness
// fails the verification. The warnings are pinned here because a pass test takes no annotations.

#[thrust_macros::requires(witness(exists(|k: i64| n == k), n))] //~ WARN: this `witness` is read as its formula here
fn in_requires(n: i64) -> i64 {
    n
}

fn in_assume(n: i64) {
    thrust_macros::assume!(|n: i64| witness(exists(|k: i64| n == k), n)); //~ WARN: this `witness` is read as its formula here
    //~^ WARN: `assume!` is assumed without proof
}

fn under_or(n: i64) {
    thrust_macros::proof_assert!(|n: i64| n == n || witness(exists(|k: i64| n == k), n)); //~ WARN: this `witness` is read as its formula here
}

fn checked(n: i64) {
    let k = thrust_macros::choose!(|n: i64| -> i64 { exists(|k: i64| n == k) });
    thrust_macros::proof_assert!(|n: i64| n == n && witness(exists(|k: i64| n == k), n + 1));
}

fn main() {
    in_requires(1);
    in_assume(1);
    under_or(1);
    checked(1);
}
