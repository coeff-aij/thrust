//@error-in-other-file: Timeout
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_SOLVER_TIMEOUT_SECS=60

// The loop of `tests/ui/pass/iterators/for_generic_count_structural_invariant.rs` with `no_structural_invariant!()`: without
// the structural invariant (`produces(iter_old, produced, iter)`) the inferred invariant cannot
// relate the count to the sequence the iterator produces, and the solver gives no answer. The
// opt-out removes only the facts Thrust adds.

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
        thrust_macros::no_structural_invariant!();
        c += 1;
    }
    c
}

fn main() {
    count(0..10i64);
}
