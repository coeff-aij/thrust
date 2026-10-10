//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::forall;
use thrust_models::model::{Int, UInt};

// Pigeonhole: when every value below `b` occurs at most once, at most `b` entries are below
// `b`. By induction on `b`, using `l3` at each step.

#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn occ(x: usize, s: &[usize], k: usize) -> usize {
    if k <= 0 {
        0
    } else {
        occ(x, s, k - 1) + if s[k - 1] == x { 1 } else { 0 }
    }
}

#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn cnt_lt(s: &[usize], k: usize, b: usize) -> usize {
    if k <= 0 {
        0
    } else {
        cnt_lt(s, k - 1, b) + if s[k - 1] < b { 1 } else { 0 }
    }
}

#[thrust_macros::predicate]
fn nonneg(s: &[usize], k: usize) -> bool {
    forall(|i: Int| !(0 <= i && i < k) || s[i] >= 0)
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(cnt_lt(s, k, b + 1) == cnt_lt(s, k, b) + occ(b, s, k))]
fn l3(s: &[usize], k: usize, b: usize) {
    if k > 0 {
        l3(s, k - 1, b);
    }
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(b == 0 && nonneg(s, k))]
#[thrust_macros::ensures(cnt_lt(s, k, b) == 0)]
fn l0(s: &[usize], k: usize, b: usize) {
    if k > 0 {
        l0(s, k - 1, b);
    }
}

#[thrust_macros::lemma]
#[thrust_macros::variant(b)]
#[thrust_macros::requires(nonneg(s, n) && forall(|x: UInt| !(x < b) || occ(x, s, n) <= 1))]
#[thrust_macros::ensures(cnt_lt(s, n, b) <= b)]
fn l5(s: &[usize], n: usize, b: usize) {
    if b > 0 {
        l5(s, n, b - 1);
        l3(s, n, b - 1);
    } else {
        l0(s, n, b);
    }
}

fn main() {}
