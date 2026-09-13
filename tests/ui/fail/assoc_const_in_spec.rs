//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// Dividing by a divisor that is not a constant leaves two obligations, because rustc
// guards the division against a zero divisor and against the single quotient that does
// not exist. A specification can now state exactly that, naming the smallest integer the
// way Rust itself names it.

#[thrust_macros::requires(d != 0 && (x != i64::MIN || d != -1))]
#[thrust_macros::ensures(result == x / d)]
fn divide(x: i64, d: i64) -> i64 {
    x / d
}

#[thrust_macros::requires(d != 0 && (x != i64::MIN || d != -1))]
#[thrust_macros::ensures(result == x % d)]
fn remainder(x: i64, d: i64) -> i64 {
    x % d
}

// The one excluded pair is the only one excluded: every other dividend divided by -1 is
// its negation.
#[thrust_macros::requires(x >= i64::MIN)]
#[thrust_macros::ensures(result == -x)]
fn negate_by_dividing(x: i64) -> i64 {
    x / -1
}

// The constant carries its value into the formula and not merely its name: the body
// writes the same number out as a literal.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == i64::MIN + 1)]
fn smallest_plus_one(_x: i64) -> i64 {
    -9223372036854775807
}

// A constant of this crate's own is read the same way.
const STEP: i64 = 4;

#[thrust_macros::requires(x >= 0)]
#[thrust_macros::ensures(result == x + 4)]
fn advance(x: i64) -> i64 {
    x + STEP
}

fn main() {
    assert!(divide(7, 2) == 3);
    assert!(remainder(7, 2) == 1);
}
