//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An `Fn` bound on the impl that declares the parameter makes its `hist_inv!` relation the
// equality of states in every method.
struct W<F>(F);

#[thrust_macros::context]
impl<F: Fn() -> i64> W<F> {
    #[thrust_macros::requires(thrust_macros::hist_inv!(f, g))]
    #[thrust_macros::ensures(f == g)]
    fn same(f: F, g: F) {}
}

fn main() {}
