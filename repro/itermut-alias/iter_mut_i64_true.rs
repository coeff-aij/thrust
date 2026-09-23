// Correct verdict: verified. The same program stating the true claim, about the final value
// of the slice rather than its entry value. It shows the specifications are not vacuous.
//
// `iter_mut`'s postcondition makes the iterator's first component the prophecy pair of the
// caller's `&mut [i64]`, and `next` hands the element at the cursor out as a `Mut` of the two
// arrays while stating that the component does not change, so a write constrains only the
// final array. `it` goes out of scope at the end of the body.

impl<'a> thrust_models::Model for core::slice::IterMut<'a, i64> {
    type Ty = (
        thrust_models::model::Mut<thrust_models::model::Seq<thrust_models::model::Int>>,
        thrust_models::model::Int,
    );
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.0 == slice && result.1 == 0)]
fn _extern_spec_slice_iter_mut(slice: &mut [i64]) -> core::slice::IterMut<'_, i64> {
    <[i64]>::iter_mut(slice)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    ((*it).1 < (*(*it).0).length
        && result == Some(thrust_models::model::Mut::new(
            (*(*it).0).array[(*it).1],
            (!(*it).0).array[(*it).1],
        ))
        && (!it).0 == (*it).0
        && (!it).1 == (*it).1 + 1)
    || ((*it).1 >= (*(*it).0).length && result == None && !it == *it)
)]
fn _extern_spec_slice_iter_mut_next<'a>(
    it: &mut core::slice::IterMut<'a, i64>,
) -> Option<&'a mut i64> {
    <core::slice::IterMut<'a, i64> as std::iter::Iterator>::next(it)
}

#[thrust_macros::requires((*s).length > 0)]
#[thrust_macros::ensures((!s).array[0] == v)]
fn set_head(s: &mut [i64], v: i64) {
    let mut it = s.iter_mut();
    if let Some(x) = it.next() {
        *x = v;
    }
}

fn main() {}
