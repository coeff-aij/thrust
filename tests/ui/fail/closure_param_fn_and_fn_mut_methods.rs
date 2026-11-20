//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::{forall, model::{Closure, Mut}};

// One method bounds the impl's parameter by `Fn` and another by `FnMut`. Both read one
// postcondition of `F`, over the states before and after a call: a call through `&` reads it at
// two equal states.
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
    #[thrust_macros::ensures(thrust_macros::hist_inv!(*f, !f))]
    #[thrust_macros::ensures(thrust_macros::post!(Mut::new(*f, !f)(), result))]
    fn call_mut(f: &mut F) -> i64
    where
        F: FnMut() -> i64,
    {
        f()
    }
}

fn main() {
    let n: i64 = 3;
    let mut c = || n;
    let a = W::call(&c);
    let b = W::call_mut(&mut c);
    assert!(a == 3 && b == 4);
}
