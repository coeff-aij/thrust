//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// `slice::IterMut` at a type parameter element type. Its first component is the prophecy pair
// of the `&mut [T]` it was made from, so the final value of every element is fixed the moment
// the iterator is made, and `next` hands out the element at the cursor as the `Mut` pair of the
// two arrays there. Writing through that element is what pins the final array down.
//
// Because the final array is a term of the model rather than a sequence that shifts as the
// iterator advances, a statement about every element it will ever hold is writable directly:
// the invariant quantifies over the positions already passed and the postcondition over all of
// them.

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
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: core::slice::IterMut<'_, T>, v: T, s: thrust_models::FnParam<&mut [T]>|
                it.0 == s.at_entry()
                    && it.1 <= (*it.0).len()
                    && forall(|j: Int| (0 <= j && j < it.1) ==> ((!it.0)[j] == v))
        );
        *x = v;
    }
}

fn main() {}
