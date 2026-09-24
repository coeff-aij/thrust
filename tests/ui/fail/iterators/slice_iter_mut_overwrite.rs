//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The first element is stepped over before the loop starts, so it keeps whatever the caller
// passed in, and the claim that every element ends up equal to `v` is false of every slice
// whose first element differs from `v`.

use thrust_models::forall;
use thrust_models::model::Int;

#[thrust_macros::context]
#[thrust_macros::requires((*s).len() >= 0)]
#[thrust_macros::ensures(
    (!s).len() == (*s).len()
        && forall(|j: Int| (0 <= j && j < (!s).len()) ==> ((!s)[j] == v))
)]
fn overwrite<T>(s: &mut [T], v: T)
    where T: thrust_models::Model + Copy, T::Ty: PartialEq
{
    let mut it = s.iter_mut();
    let _skipped = it.next();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: core::slice::IterMut<'_, T>, v: T, s: thrust_models::FnParam<&mut [T]>|
                it.0 == *s.at_entry()
                    && it.1 == !s.at_entry()
                    && it.1.len() == it.0.len()
                    && it.2 <= it.0.len()
                    && forall(|j: Int| (0 <= j && j < it.2) ==> (it.1[j] == v))
        );
        *x = v;
    }
}

fn main() {}
