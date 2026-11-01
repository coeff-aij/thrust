//@compile-flags: -C debug-assertions=off

// An equality of two formulas has no term form, so it cannot be cast to an integer.

#[thrust_macros::predicate]
fn positive(x: i32) -> bool {
    x > 0
}

#[thrust_macros::predicate]
fn large(x: i32) -> bool {
    x > 1
}

#[thrust_macros::ensures((positive(x) == large(x)) as i32 == 1)] //~ ERROR: is a formula, not a value
fn check(x: i32) {
    let _ = x;
}

fn main() {
    check(3);
}
