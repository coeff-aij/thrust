//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_SPLIT_GOALS=1

// The fail twin of advance_by.rs: the error counts one item fewer than are left.
// std's default `Iterator::advance_by` (core/src/iter/traits/iterator.rs, toolchain 1.94.1), with
// std's body, as a free function over std.rs's `IteratorSpec`. Deviations: the error is `usize` for
// `NonZero<usize>` (std builds it with `NonZero::new_unchecked(n - i)`), and the specialisation
// trait `SpecAdvanceBy`, whose default method is this body, is left out. `Ok(())`: the iterator
// produced `n` items; `Err(k)`: it produced `n - k` items and then completed, with `0 < k <= n`.
use thrust_models::model::{Mut, Seq};
use thrust_models::{exists, forall, Ghost, Model};

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(*it))]
#[thrust_macros::ensures(I::inv(!it))]
#[thrust_macros::ensures(result == Ok(()) ==> exists(|s: Seq<<I::Item as Model>::Ty>| s.len() == n && I::produces(*it, s, !it)))]
#[thrust_macros::ensures(forall(|k: <usize as Model>::Ty| result == Err(k) ==> (0 < k && k <= n
    && exists(|s: Seq<<I::Item as Model>::Ty>, mid: <I as Model>::Ty|
        s.len() == n - k && I::produces(*it, s, mid) && I::completed(Mut::new(mid, !it))))))]
fn advance_by<I: IteratorSpec>(it: &mut I, n: usize) -> Result<(), usize>
where
    I::Item: Model,
{
    let old_it = thrust_macros::ghost!(|it: &mut I| -> I { *it });
    for i in 0..n {
        thrust_macros::partial_invariant!(|iter: core::ops::Range<usize>, iter_old: Ghost<core::ops::Range<usize>>, produced: Ghost<Seq<<usize as Model>::Ty>>, it: &mut I, old_it: Ghost<I>, n: usize|
            iter_old.start == 0 && iter_old.end == n && I::inv(*it)
                && exists(|s: Seq<<I::Item as Model>::Ty>| s.len() == produced.len() && I::produces(old_it, s, *it)));
        if it.next().is_none() {
            return Err(n - i - 1);
        }
    }
    Ok(())
}

#[thrust_macros::context]
#[thrust::callable]
fn advance_three() {
    let mut r = 0..10i64;
    let res = advance_by(&mut r, 3);
    match res {
        Ok(()) => assert!(r.start == 3),
        Err(_) => assert!(false),
    }
}

fn main() {}
