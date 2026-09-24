//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// Rust's `/` truncates toward zero and its `%` takes the sign of the dividend, so for a
// negative dividend both go the opposite way from the never-negative remainder that
// SMT-LIB's own division would leave.

#[thrust_macros::requires(x == -7)]
#[thrust_macros::ensures(result == -3)]
fn quotient_of_negative(x: i64) -> i64 {
    x / 2
}

#[thrust_macros::requires(x == -7)]
#[thrust_macros::ensures(result == 1)]
fn remainder_of_negative(x: i64) -> i64 {
    x % 2
}

// Quotient and remainder still fit back together, whatever the sign of the dividend.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x)]
fn quotient_and_remainder_reconstruct(x: i64) -> i64 {
    (x / 2) * 2 + x % 2
}

// The same identity stated in the specification rather than the body.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x - (x / 2) * 2)]
fn remainder_agrees_with_quotient(x: i64) -> i64 {
    x % 2
}

// Only a non-negative dividend keeps the remainder non-negative.
#[thrust_macros::requires(x >= 0)]
#[thrust_macros::ensures(result == 0 || result == 1)]
fn remainder_of_non_negative(x: i64) -> i64 {
    x % 2
}

// The predicate a filter is usually given.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (x % 2 == 0))]
fn is_even(x: i64) -> bool {
    x % 2 == 0
}

// A divisor that is not a constant. The caller has to rule out zero, which rustc guards
// against, and the caller's `d > 0` here does that.
#[thrust_macros::requires(x >= 0 && d > 0)]
#[thrust_macros::ensures(result >= 0)]
fn quotient_by_positive(x: i64, d: i64) -> i64 {
    x / d
}

fn main() {}
