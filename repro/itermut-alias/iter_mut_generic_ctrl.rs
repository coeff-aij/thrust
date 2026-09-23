// Correct verdict: Unsat. The control for `iter_mut_generic.rs`: the same false claim with
// the write done by indexing instead of through the iterator. `(*s).array[0]` is the entry value of the slice, which the body
// never reads; it writes one element through `iter_mut` and then claims the caller's input
// already held the written value.
//
// `iter_mut`'s postcondition makes the iterator's first component the prophecy pair of the
// caller's `&mut [i64]`, and `next` hands the element at the cursor out as a `Mut` of the two
// arrays while stating that the component does not change, so a write constrains only the
// final array. `it` goes out of scope at the end of the body.

impl<'a, T> thrust_models::Model for core::slice::IterMut<'a, T> where T: thrust_models::Model {
    type Ty = (
        thrust_models::model::Mut<thrust_models::model::Seq<<T as thrust_models::Model>::Ty>>,
        thrust_models::model::Int,
    );
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.0 == slice && result.1 == 0)]
fn _extern_spec_slice_iter_mut<T>(slice: &mut [T]) -> core::slice::IterMut<'_, T>
    where T: thrust_models::Model, T::Ty: PartialEq
{
    <[T]>::iter_mut(slice)
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
fn _extern_spec_slice_iter_mut_next<'a, T>(
    it: &mut core::slice::IterMut<'a, T>,
) -> Option<&'a mut T>
    where T: thrust_models::Model + 'a, T::Ty: PartialEq
{
    <core::slice::IterMut<'a, T> as std::iter::Iterator>::next(it)
}

#[thrust::callable]
#[thrust_macros::context]
#[thrust_macros::requires((*s).length > 0)]
#[thrust_macros::ensures((*s).array[0] == v)]
fn set_head<T>(s: &mut [T], v: T)
    where T: thrust_models::Model + Copy, T::Ty: PartialEq
{
    s[0] = v;
}

// A concrete call site is what makes a generic body reach the solver on this branch; the
// slice comes from a trusted provider because array indexing is not modelled here.
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((*result).length > 0)]
fn some_slice<'a>() -> &'a mut [i64] {
    unimplemented!()
}

fn main() {
    let s = some_slice();
    set_head(s, 7);
}
