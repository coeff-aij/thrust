//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::{forall, model::Closure};

// An `Fn` bound on the impl makes a call in a method that also bounds the parameter by `FnMut` a
// call through `&`, which keeps the closure's state.
struct W<F>(F);

#[thrust_macros::context]
impl<F: Fn() -> i64> W<F> {
    #[thrust_macros::requires(thrust_macros::pre!(f()))]
    #[thrust_macros::ensures(thrust_macros::post!(f(), result))]
    fn call(f: &F) -> i64 {
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
