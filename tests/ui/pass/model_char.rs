//@check-pass
//@compile-flags: -Adead_code -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The model of a `char` is itself: a contract can state the `char`s of a `Vec<char>`, and
// `ghost!` and `choose!` can make a `char`.
use thrust_models::{exists, forall, Ghost};

#[thrust_macros::ensures(forall(|i: thrust_models::model::Int|
    (0 <= i && i < (*v).len()) ==> (*v)[i] <= char::MAX))]
fn chars_in_range(v: &Vec<char>) {}

#[thrust_macros::predicate]
fn max_exists(n: i64) -> bool {
    exists(|c: char| n == 0 && c == char::MAX)
}

#[thrust_macros::requires(max_exists(n))]
#[thrust_macros::ensures(true)]
fn by_choose(n: i64) {
    let c = thrust_macros::choose!(|n: i64| -> char { max_exists(n) });
    thrust_macros::proof_assert!(|c: Ghost<char>| c == char::MAX);
}

fn by_ghost(c: char) {
    let g = thrust_macros::ghost!(|c: char| -> char { c });
    thrust_macros::proof_assert!(|g: Ghost<char>, c: char| g == c);
}

fn main() {
    by_choose(0);
    by_ghost('a');
}
