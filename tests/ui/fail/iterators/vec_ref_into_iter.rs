//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// The loop visits each element of the vector exactly once, so it counts the length and not one
// more than the length. A vector of length 0 already refutes the claim.

#[thrust_macros::context]
#[thrust_macros::requires((*v).length >= 0)]
#[thrust_macros::ensures(result == (*v).length + 1)]
fn count(v: &Vec<i64>) -> usize {
    let mut it = (&*v).into_iter();
    let mut n = 0;
    while let Some(_x) = it.next() {
        thrust_macros::invariant!(|it: core::slice::Iter<'_, i64>, n: usize, v: &Vec<i64>|
            it.0 == *v && n == it.1 && it.1 <= it.0.length);
        n = n + 1;
    }
    assert!(n == v.len() + 1);
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
                it.0 == *v.at_entry()
                    && it.1 == !v.at_entry()
                    && it.1.length == it.0.length
                    && it.2 <= it.0.length);
        *x = 0;
    }
}

fn main() {}
