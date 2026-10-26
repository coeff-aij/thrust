//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `for` over `it.by_ref()` whose invariant names the history: the ghost `iter_old` holds the
// `&mut`, and its death at the loop's exit does not resolve the borrow `it` is under, which the
// loop's iterator resolves when it dies. The invariant is partial, so the inferred part relates
// `it` to the reference.

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn drain() {
    let mut it = 0..3i64;
    for _x in it.by_ref() {
        thrust_macros::partial_invariant!(|iter: &mut core::ops::Range<i64>, iter_old: Ghost<&mut core::ops::Range<i64>>, produced: Ghost<Seq<Int>>|
            (*iter_old).start == 0 && (*iter_old).end == 3);
    }
    assert!(it.start == 3);
}

fn main() {}
