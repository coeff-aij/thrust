//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::forall;
use thrust_models::model::{Int, UInt};

// After the loop, `proof!` applies `below_count`, built from the counting lemmas: at least
// `n - b` of `n` distinct values below `n` are at least `b`, so `high` can be indexed at
// `n - b - 1`.

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

#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn cnt_ge(s: &[usize], k: usize, b: usize) -> usize {
    if k <= 0 {
        0
    } else {
        cnt_ge(s, k - 1, b) + if s[k - 1] >= b { 1 } else { 0 }
    }
}

#[thrust_macros::predicate]
fn distinct(s: &[usize], k: usize) -> bool {
    forall(|i: Int, j: Int| !(0 <= i && i < j && j < k) || s[i] != s[j])
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

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(cnt_lt(s, k, b) + cnt_ge(s, k, b) == k)]
fn l6(s: &[usize], k: usize, b: usize) {
    if k > 0 {
        l6(s, k - 1, b);
    }
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(k <= s.len() && distinct(s, k))]
#[thrust_macros::ensures(forall(|x: UInt| occ(x, s, k) <= 1))]
fn l4_all(s: &[usize], k: usize) {
    if k > 0 {
        l4_all(s, k - 1);
        absent(s[k - 1], s, k - 1);
    }
}

#[thrust_macros::predicate]
fn distinct_below(s: &[usize], n: usize) -> bool {
    n == s.len()
        && distinct(s, n)
        && forall(|i: Int| !(0 <= i && i < n) || (0 <= s[i] && s[i] < n))
}

#[thrust_macros::lemma]
#[thrust_macros::requires(b <= n && distinct_below(s, n))]
#[thrust_macros::ensures(cnt_ge(s, n, b) >= n - b)]
fn below_count(s: &[usize], n: usize, b: usize) {
    l4_all(s, n);
    l5(s, n, b);
    l6(s, n, b);
}

#[thrust_macros::requires(b < n && distinct_below(s, n))]
fn last_high(s: &[usize], n: usize, b: usize) -> usize {
    let mut low: Vec<usize> = Vec::new();
    let mut high: Vec<usize> = Vec::new();
    let mut t = 0;
    while t < n {
        thrust_macros::invariant!(|s: &[usize], n: usize, b: usize, t: usize, high: Vec<usize>| {
            t <= n && b < n && distinct_below(s, n) && high.len() == cnt_ge(s, t, b)
        });
        if s[t] < b {
            low.push(s[t]);
        } else {
            high.push(s[t] - b);
        }
        t += 1;
    }
    thrust_macros::proof!(below_count(s, n, b));
    high[n - b]
}

fn main() {}
