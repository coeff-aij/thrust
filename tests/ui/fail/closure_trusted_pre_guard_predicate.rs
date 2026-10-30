//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A predicate that uses a `pre!` only as a guard (`!total(g) || ..`) does not ask for it, so the
// closure must accept every argument.

#[thrust_macros::predicate]
fn total<G: Fn(i32)>(g: G) -> bool {
    thrust_models::forall(|y: <i32 as thrust_models::Model>::Ty| thrust_macros::pre!(g(y)))
}

#[thrust_macros::predicate]
fn positive_if_total<G: Fn(i32)>(g: G, x: i32) -> bool {
    !total(g) || x > 0
}

#[thrust::trusted]
#[thrust_macros::requires(positive_if_total(f, x))]
#[thrust_macros::ensures(true)]
fn apply<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn main() {
    apply(|x: i32| assert!(x > 0), 0);
}
