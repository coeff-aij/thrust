//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `fulcrum` (`examples/hillel.rs`, 3620de437), with Creusot's code and Thrust's
// annotations: two `for` loops over `s` and `0..s.len()`. `sum_range`, `score` and the lemma
// `sum_range_split` are Creusot's logic functions; `score`'s two `ensures` are the lemma
// `score_bounds`. std.rs has no specification of `u32::abs_diff` (only `i32::abs_diff`), which
// `fulcrum` calls, so this file stops at that call; `hillel_fulcrum_abs_diff.rs` gives the call
// the contract of `i32::abs_diff` through a trusted local function, to check the rest.
use thrust_models::forall;
use thrust_models::model::{int_lit, Seq, UInt};
use thrust_models::{FnParam, Ghost};

#[thrust_macros::logic]
#[thrust_macros::variant(to - from)]
fn sum_range(s: &[u32], from: usize, to: usize) -> u32 {
    if to > from {
        s[from] + sum_range(s, from + 1, to)
    } else {
        0
    }
}

#[thrust_macros::lemma]
#[thrust_macros::variant(i - from)]
#[thrust_macros::requires(from <= i && i <= to && to <= s.len())]
#[thrust_macros::ensures(sum_range(s, from, to) == sum_range(s, from, i) + sum_range(s, i, to))]
fn sum_range_split(s: &[u32], from: usize, to: usize, i: usize) {
    if i > from {
        sum_range_split(s, from + 1, to, i);
    }
}

#[thrust_macros::logic]
fn score(s: &[u32], i: usize) -> u32 {
    if sum_range(s, int_lit::<UInt>(0), i) >= sum_range(s, i, s.len()) {
        sum_range(s, int_lit::<UInt>(0), i) - sum_range(s, i, s.len())
    } else {
        sum_range(s, i, s.len()) - sum_range(s, int_lit::<UInt>(0), i)
    }
}

#[thrust_macros::lemma]
#[thrust_macros::requires(i <= s.len())]
#[thrust_macros::ensures(
    score(s, i) <= sum_range(s, int_lit::<UInt>(0), s.len())
        && ((i == 0 || i == s.len()) ==> score(s, i) == sum_range(s, int_lit::<UInt>(0), s.len()))
)]
fn score_bounds(s: &[u32], i: usize) {
    sum_range_split(s, 0, s.len(), i);
}

#[thrust_macros::context]
#[thrust_macros::requires(sum_range(s, int_lit::<UInt>(0), s.len()) <= 1000)]
#[thrust_macros::requires(s.len() > 0)]
#[thrust_macros::ensures(result < s.len())]
#[thrust_macros::ensures(forall(|i: UInt| !(i < s.len()) || score(s, result) <= score(s, i)))]
fn fulcrum(s: &[u32]) -> usize {
    let mut total: u32 = 0;

    for &x in s {
        thrust_macros::invariant!(|iter: core::slice::Iter<'_, u32>, iter_old: Ghost<core::slice::Iter<'_, u32>>, produced: Ghost<Seq<&UInt>>, total: u32, s: &[u32]|
            iter_old.0 == *s && iter_old.1 == int_lit::<UInt>(0)
                && total == sum_range(s, int_lit::<UInt>(0), produced.len())
                && total <= sum_range(s, int_lit::<UInt>(0), s.len()));
        total += x;
    }

    let mut min_i: usize = 0;
    let mut min_dist: u32 = total;

    let mut sum: u32 = 0;
    for i in 0..s.len() {
        thrust_macros::invariant!(|iter: core::ops::Range<usize>, iter_old: Ghost<core::ops::Range<usize>>, produced: Ghost<Seq<UInt>>, sum: u32, total: u32, min_i: usize, min_dist: u32, s: &[u32]|
            iter_old.start == 0 && iter_old.end == s.len()
                && total == sum_range(s, int_lit::<UInt>(0), s.len())
                && sum == sum_range(s, int_lit::<UInt>(0), produced.len())
                && sum <= total
                && min_i <= produced.len() && min_i < s.len()
                && min_dist == score(s, min_i)
                && forall(|j: UInt| !(j < produced.len()) || score(s, min_i) <= score(s, j)));
        let dist = sum.abs_diff(total - sum);
        if dist < min_dist {
            min_i = i;
            min_dist = dist;
        }

        sum += s[i];
    }

    min_i
}
