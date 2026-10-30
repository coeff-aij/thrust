//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The twin of `pass/closure_trusted_pre_predicate.rs`: the `pre!` stated through the predicate
// does not hold at the call.

#[thrust_macros::predicate]
fn pre_at<G: Fn(i32)>(g: G, x: i32) -> bool {
    thrust_macros::pre!(g(x))
}

#[thrust::trusted]
#[thrust_macros::requires(pre_at(f, x))]
#[thrust_macros::ensures(true)]
fn apply_pre<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn main() {
    apply_pre(|x: i32| assert!(x > 0), 0);
}
