//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The index `enumerate` pairs with an element is a position of the sequence.

#[thrust_macros::context]
#[thrust_macros::requires((*v).len() >= 0)]
fn indices(v: &Vec<i64>) {
    let mut it = v.iter().enumerate();
    while let Some((i, _x)) = it.next() {
        thrust_macros::invariant!(|it: core::iter::Enumerate<core::slice::Iter<'_, i64>>, v: &Vec<i64>|
            it.0.0 == *v && it.0.1 == it.1 && it.1 <= it.0.0.len());
        assert!(i < v.len());
    }
}

fn main() {}
