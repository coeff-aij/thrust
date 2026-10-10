//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::forall;
use thrust_models::model::Int;

// Among pairwise distinct entries a value occurs at most once.

#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn occ(x: usize, s: &[usize], k: usize) -> usize {
    if k <= 0 {
        0
    } else {
        occ(x, s, k - 1) + if s[k - 1] == x { 1 } else { 0 }
    }
}

#[thrust_macros::predicate]
fn distinct(s: &[usize], k: usize) -> bool {
    forall(|i: Int, j: Int| !(0 <= i && i < j && j < k) || s[i] != s[j])
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(forall(|i: Int| !(0 <= i && i < k) || s[i] != x))]
#[thrust_macros::ensures(occ(x, s, k) == 0)]
fn absent(x: usize, s: &[usize], k: usize) {
    if k > 0 {
        absent(x, s, k - 1);
    }
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(k <= s.len() && distinct(s, k))]
#[thrust_macros::ensures(occ(x, s, k) <= 1)]
fn l4(x: usize, s: &[usize], k: usize) {
    if k > 0 {
        if s[k - 1] == x {
            absent(x, s, k - 1);
        } else {
            l4(x, s, k - 1);
        }
    }
}

fn main() {}
