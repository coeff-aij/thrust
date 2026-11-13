//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// The fail twin of `hillel_fulcrum_is_min.rs`: `fulcrum` also claims the index is 0.
// Creusot's `fulcrum` (`examples/hillel.rs`, 3620de437), with Creusot's code and Thrust's
// annotations: two `for` loops over `s` and `0..s.len()`. `sum_range`, `score` and the lemma
// `sum_range_split` are Creusot's logic functions; `score`'s two `ensures` are the lemma
// `score_bounds`; `sum_range_nonneg` and `sum_range_snoc` is the instance of `sum_range_split` that the loops' steps use.
// The postcondition's `forall` is stated through `is_min`, its recursive form; `hillel_fulcrum.rs`
// states it as Creusot does.
use thrust_models::forall;
use thrust_models::model::{int_lit, Seq, UInt};
use thrust_models::{FnParam, Ghost};

#[thrust_macros::logic]
#[thrust_macros::variant(to - from)]
fn sum_range(s: &[u32], from: usize, to: usize) -> i64 {
    if to > from {
        sum_range(s, from + 1, to) + s[from]
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

#[thrust_macros::lemma]
#[thrust_macros::requires(k < s.len())]
#[thrust_macros::ensures(sum_range(s, int_lit::<UInt>(0), k + 1) == sum_range(s, int_lit::<UInt>(0), k) + s[k])]
fn sum_range_snoc(s: &[u32], k: usize) {
    sum_range_split(s, 0, k + 1, k);
}

#[thrust_macros::logic]
fn score(s: &[u32], i: usize) -> i64 {
    if sum_range(s, int_lit::<UInt>(0), i) >= sum_range(s, i, s.len()) {
        sum_range(s, int_lit::<UInt>(0), i) - sum_range(s, i, s.len())
    } else {
        sum_range(s, i, s.len()) - sum_range(s, int_lit::<UInt>(0), i)
    }
}

// A `u32` is not negative; the model of a slice of `u32` does not say so of its elements (the
// range facts are assumed of scalars and, with `THRUST_INT_RANGE`, of elements), where Creusot's
// `u32@` is in range.
#[thrust_macros::lemma]
#[thrust::trusted]
#[thrust_macros::requires(i < s.len())]
#[thrust_macros::ensures(s[i] >= 0)]
fn elem_nonneg(s: &[u32], i: usize) {}

#[thrust_macros::lemma]
#[thrust_macros::variant(to - from)]
#[thrust_macros::requires(from <= to && to <= s.len())]
#[thrust_macros::ensures(sum_range(s, from, to) >= 0)]
fn sum_range_nonneg(s: &[u32], from: usize, to: usize) {
    if to > from {
        sum_range_nonneg(s, from + 1, to);
        elem_nonneg(s, from);
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
    sum_range_nonneg(s, 0, i);
    sum_range_nonneg(s, i, s.len());
}

// No `j < k` has a score below that of `m`, by recursion on `k`, as `sum_range` is: the loops'
// invariant, whose steps are the lemmas below.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn is_min(s: &[u32], m: usize, k: usize) -> bool {
    if k <= 0 {
        true
    } else {
        is_min(s, m, k - 1) && score(s, m) <= score(s, k - 1)
    }
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(is_min(s, m, k) && score(s, m2) <= score(s, m))]
#[thrust_macros::ensures(is_min(s, m2, k))]
fn min_replace(s: &[u32], m: usize, m2: usize, k: usize) {
    if k > 0 {
        min_replace(s, m, m2, k - 1);
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(sum_range(s, int_lit::<UInt>(0), s.len()) <= 1000)]
#[thrust_macros::requires(s.len() > 0)]
#[thrust_macros::ensures(result < s.len())]
#[thrust_macros::ensures(is_min(s, result, s.len()) && result == 0)]
fn fulcrum(s: &[u32]) -> usize {
    let mut total: u32 = 0;

    thrust_macros::proof!(sum_range_nonneg(s, 0, s.len()));
    let mut k: usize = 0;
    for &x in s {
        thrust_macros::invariant!(|iter: core::slice::Iter<'_, u32>, iter_old: Ghost<core::slice::Iter<'_, u32>>, produced: Ghost<Seq<&UInt>>, total: u32, s: &[u32], k: usize|
            iter_old.0 == *s && iter_old.1 == int_lit::<UInt>(0)
                && k == produced.len() && s.len() > 0
                && total == sum_range(s, int_lit::<UInt>(0), produced.len())
                && total <= sum_range(s, int_lit::<UInt>(0), s.len()));
        thrust_macros::proof!(sum_range_snoc(s, k));
        thrust_macros::proof!(sum_range_split(s, 0, s.len(), k + 1));
        thrust_macros::proof!(sum_range_nonneg(s, k + 1, s.len()));
        total += x;
        k += 1;
    }

    let mut min_i: usize = 0;
    let mut min_dist: u32 = total;

    let mut sum: u32 = 0;
    for i in 0..s.len() {
        thrust_macros::invariant!(|iter: core::ops::Range<usize>, iter_old: Ghost<core::ops::Range<usize>>, produced: Ghost<Seq<UInt>>, sum: u32, total: u32, min_i: usize, min_dist: u32, s: &[u32]|
            iter_old.start == 0 && iter_old.end == s.len() && produced.len() <= s.len()
                && total == sum_range(s, int_lit::<UInt>(0), s.len())
                && sum == sum_range(s, int_lit::<UInt>(0), produced.len())
                && sum <= total
                && min_i <= produced.len() && min_i < s.len()
                && min_dist == score(s, min_i)
                && is_min(s, min_i, produced.len()));
        thrust_macros::proof!(sum_range_snoc(s, i));
        thrust_macros::proof!(sum_range_split(s, 0, s.len(), i));
        thrust_macros::proof!(sum_range_split(s, 0, s.len(), i + 1));
        thrust_macros::proof!(sum_range_nonneg(s, i + 1, s.len()));
        thrust_macros::proof!(sum_range_nonneg(s, 0, i));
        let dist = sum.abs_diff(total - sum);
        if dist < min_dist {
            thrust_macros::proof!(min_replace(s, min_i, i, i));
            min_i = i;
            min_dist = dist;
        }

        sum += s[i];
    }

    min_i
}
