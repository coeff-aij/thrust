//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `pre!` that the trusted function's `requires` states through a predicate counts as stated, as
// one written in the `requires` does: the closure need not accept other arguments. The predicate's
// own type parameter `G` is read at the call's argument `F`.

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
    apply_pre(|x: i32| assert!(x > 0), 1);
}
