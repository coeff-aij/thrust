//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `for` loop without a written invariant over a generic iterator: the postcondition names the
// sequence the iterator produces, so the inferred invariant relates the count to the loop's
// `produced`, which `#[thrust_macros::context]` keeps as for an annotated loop.

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
