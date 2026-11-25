//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An `Fn` bound on one method does not make the `hist_inv!` relation of the impl's parameter the
// equality of states: the relation is shared by every method of the impl, and another may bound
// the parameter by `FnMut` only.
struct W<F>(F);

#[thrust_macros::context]
impl<F> W<F> {
    #[thrust_macros::requires(thrust_macros::hist_inv!(f, g))]
    #[thrust_macros::ensures(f == g)]
    fn same(f: F, g: F)
    where
        F: Fn() -> i64,
    {
    }
}

fn main() {}
