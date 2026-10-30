//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `pre!` stated two predicates deep counts as stated: each receiver is read at its call's
// generic arguments, the inner call's and then the outer one's.

#[thrust_macros::predicate]
fn inner<G: Fn(i32)>(g: G, x: i32) -> bool {
    thrust_macros::pre!(g(x))
}

#[thrust_macros::predicate]
fn outer<H: Fn(i32)>(h: H, x: i32) -> bool {
    inner(h, x)
}

#[thrust::trusted]
#[thrust_macros::requires(outer(f, x))]
#[thrust_macros::ensures(true)]
fn apply<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn main() {
    apply(|x: i32| assert!(x > 0), 1);
}
