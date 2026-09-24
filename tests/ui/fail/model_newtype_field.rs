//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `size` reports one more element than the sequence holds, which its postcondition ties to
// the length the whole value carries.

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
#[thrust_macros::ensures(result == (*v).len())]
fn size(v: &IndexVec<Idx, i64>) -> usize {
    v.raw.len() + 1
}

#[thrust_macros::context]
#[thrust_macros::ensures(result.len() == raw.len())]
fn wrap(raw: Vec<i64>) -> IndexVec<Idx, i64> {
    IndexVec {
        raw,
        _marker: PhantomData,
    }
}

#[thrust_macros::context]
#[thrust_macros::ensures((!v).len() == (*v).len() + 1)]
fn push(v: &mut IndexVec<Idx, i64>, x: i64) {
    v.raw.push(x);
}

fn main() {
    let mut v = wrap(Vec::new());
    assert!(size(&v) == 0);
    push(&mut v, 7);
    assert!(size(&v) == 1);
}
