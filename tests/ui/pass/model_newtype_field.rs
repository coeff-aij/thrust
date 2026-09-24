//@check-pass
//@compile-flags: -C debug-assertions=off

// A struct whose `Model::Ty` is the model of one of its fields is that field in the logic:
// the struct never survives to be traversed, so the field access is the identity and not a
// projection. Without that, `raw`'s index and the first component of the `(array, length)`
// pair the model is are both `0`, and `.raw` comes back as the element array.
//
// Each of the three functions pins the field against the whole value from a different side:
// reading it, building the struct out of it, and writing through it.

use std::marker::PhantomData;

struct Idx;

struct IndexVec<I, T> {
    raw: Vec<T>,
    _marker: PhantomData<fn(&I)>,
}

impl<I, T> thrust_models::Model for IndexVec<I, T>
where
    T: thrust_models::Model,
{
    type Ty = <[T] as thrust_models::Model>::Ty;
}

#[thrust_macros::context]
#[thrust_macros::ensures(result == (*v).length)]
fn size(v: &IndexVec<Idx, i64>) -> usize {
    v.raw.len()
}

#[thrust_macros::context]
#[thrust_macros::ensures(result.length == raw.length)]
fn wrap(raw: Vec<i64>) -> IndexVec<Idx, i64> {
    IndexVec {
        raw,
        _marker: PhantomData,
    }
}

#[thrust_macros::context]
#[thrust_macros::ensures((!v).length == (*v).length + 1)]
fn push(v: &mut IndexVec<Idx, i64>, x: i64) {
    v.raw.push(x);
}

fn main() {
    let mut v = wrap(Vec::new());
    assert!(size(&v) == 0);
    push(&mut v, 7);
    assert!(size(&v) == 1);
}
