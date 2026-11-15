//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::exists;

struct Item {
    a: i64,
    o: Option<i64>,
}

impl thrust_models::Model for Item {
    type Ty = Self;
}

// `Item` occurs only as the type of the quantified variable, so the `Option` in its field is
// reached through no signature.
#[thrust_macros::predicate]
fn has_item_with(n: i64) -> bool {
    exists(|x: Item| x.a == n + 1 && x.a == n)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(has_item_with(result))]
fn f(n: i64) -> i64 {
    n
}

fn main() {
    f(1);
}
