//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

// The index is the number of elements before the element, so it is not one more.

#[thrust_macros::context]
#[thrust_macros::requires((*v).len() >= 0)]
fn indices(v: &Vec<i64>) {
    let mut it = v.iter().enumerate();
    let mut n = 0;
    while let Some((i, _x)) = it.next() {
        thrust_macros::invariant!(|it: core::iter::Enumerate<core::slice::Iter<'_, i64>>, n: usize|
            n == it.1 && it.0.1 == n && n <= it.0.0.len());
        assert!(i == n + 1);
        n = n + 1;
    }
}

fn main() {}
