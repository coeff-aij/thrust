//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

// Both halves of a zip over the same sequence hand out the same element.

#[thrust_macros::context]
#[thrust_macros::requires((*v).len() >= 0)]
fn same(v: &Vec<i64>) {
    let mut it = std::iter::zip(v.iter(), v.iter());
    while let Some((x, y)) = it.next() {
        thrust_macros::invariant!(|it: core::iter::Zip<core::slice::Iter<'_, i64>, core::slice::Iter<'_, i64>>|
            it.0 == it.1);
        assert!(*x == *y);
    }
}

fn main() {}
