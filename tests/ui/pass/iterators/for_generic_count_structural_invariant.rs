//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_SOLVER_TIMEOUT_SECS=60

// A `for` loop without a written invariant over a generic iterator, not instantiated per
// instance: the postcondition names the sequence the iterator produces, which the structural
// invariant (`produces(iter_old, produced, iter)`) relates to the loop's count. With it the query
// is answered; the same loop of `tests/ui/fail/iterators/for_generic_count_structural_invariant.rs` has
// `no_structural_invariant!()`, for which the solver gives no answer.

use thrust_models::model::{Mut, Seq};
use thrust_models::Model;

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(it))]
#[thrust_macros::ensures(thrust_models::exists(|s: Seq<<I::Item as Model>::Ty>, last: I::Ty, fin: I::Ty|
    I::produces(it, s, last) && I::completed(Mut::new(last, fin)) && result == s.len()))]
fn count<I: IteratorSpec>(it: I) -> usize
where
    I::Item: Model,
{
    let mut c = 0;
    for _x in it {
        
        c += 1;
    }
    c
}

fn main() {
    count(0..10i64);
}
