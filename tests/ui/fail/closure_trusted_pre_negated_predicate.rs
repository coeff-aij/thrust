//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A predicate that negates a `pre!` does not ask for it, so the closure must accept every
// argument.

#[thrust_macros::predicate]
fn refuses<G: Fn(i32)>(g: G, x: i32) -> bool {
    !thrust_macros::pre!(g(x))
}

#[thrust::trusted]
#[thrust_macros::requires(refuses(f, x))]
#[thrust_macros::ensures(true)]
fn apply<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn main() {
    apply(|x: i32| assert!(x > 0), 0);
}
