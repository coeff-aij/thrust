//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The twin of `pass/closure_trusted_pre_chain.rs`: the `pre!` stated two predicates deep does
// not hold at the call.

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
    apply(|x: i32| assert!(x > 0), 0);
}
