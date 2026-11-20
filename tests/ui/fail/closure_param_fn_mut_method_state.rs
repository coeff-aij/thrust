//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::{forall, model::Closure};

// A method that bounds the impl's parameter by `Fn` does not make a call through `&mut` in
// another method, which bounds it by `FnMut` only, keep the closure's state.
struct W<F>(F);

#[thrust_macros::context]
impl<F> W<F> {
    #[thrust_macros::requires(thrust_macros::pre!(f()))]
    #[thrust_macros::ensures(thrust_macros::post!(f(), result))]
    fn call(f: &F) -> i64
    where
        F: Fn() -> i64,
    {
        f()
    }

    #[thrust_macros::requires(forall(|c: Closure<F>| thrust_macros::pre!(c())))]
    #[thrust_macros::ensures(*f == !f)]
    fn call_mut(f: &mut F) -> i64
    where
        F: FnMut() -> i64,
    {
        f()
    }
}

fn main() {}
