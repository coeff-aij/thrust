//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// `IntoIterator` on a borrowed `Vec` hands back the two slice iterators rather than
// `vec::IntoIter`: a shared borrow yields `slice::Iter` and leaves the vector alone, a mutable
// one yields `slice::IterMut` and carries the vector's prophecy pair into the iterator.

#[thrust_macros::context]
#[thrust_macros::requires((*v).length >= 0)]
#[thrust_macros::ensures(result == (*v).length)]
fn count(v: &Vec<i64>) -> usize {
    let mut it = (&*v).into_iter();
    let mut n = 0;
    while let Some(_x) = it.next() {
        thrust_macros::invariant!(|it: core::slice::Iter<'_, i64>, n: usize, v: &Vec<i64>|
            it.0 == *v && n == it.1 && it.1 <= it.0.length);
        n = n + 1;
    }
    assert!(n == v.len());
    n
}

#[thrust_macros::context]
#[thrust_macros::requires((*v).length >= 0)]
#[thrust_macros::ensures((!v).length == (*v).length)]
fn zero(v: &mut Vec<i64>) {
    let mut it = (&mut *v).into_iter();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: core::slice::IterMut<'_, i64>, v: thrust_models::FnParam<&mut Vec<i64>>|
                it.0 == v.at_entry() && it.1 <= (*it.0).length);
        *x = 0;
    }
}

fn main() {}
