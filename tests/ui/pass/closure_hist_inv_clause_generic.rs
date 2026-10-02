//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::{exists, forall, model::{Closure, Mut}};

// `call_twice` hides the state between the calls behind `hist_inv!`, as `try_fold` does.
#[thrust_macros::requires(forall(|c: Closure<G>, y: i64| thrust_macros::pre!(c(y))))]
#[thrust_macros::ensures(exists(|c: Closure<G>, d: Closure<G>, y: i64|
    thrust_macros::hist_inv!(*g, c) && thrust_macros::post!(Mut::new(c, d)(y), result)))]
fn call_twice<G: FnMut(i64) -> i64>(g: &mut G, x: i64) -> i64 {
    let a = g(x);
    g(a)
}

// Under `#[thrust_macros::context]` a `closure!` clause may name a capture of a generic type.
// `g` owns `f`, so the relation its captures give says nothing of `f`; its `hist_inv` clause relates
// its states through `f`'s. That is what carries `call_twice`'s `hist_inv!` over `g` to one over `f`.
#[thrust_macros::context]
#[thrust_macros::requires(forall(|c: Closure<F>, y: i64| thrust_macros::pre!(c(y))))]
#[thrust_macros::ensures(exists(|c: Closure<F>, d: Closure<F>, y: i64|
    thrust_macros::hist_inv!(f, c) && thrust_macros::post!(Mut::new(c, d)(y), result)))]
fn call_twice_through<F: FnMut(i64) -> i64>(mut f: F, x: i64) -> i64 {
    let mut g = thrust_macros::closure!(
        captures(f: &mut F),
        hist_inv(thrust_macros::hist_inv!(*f, !f)),
        move |y: i64| -> i64 { f(y) },
    );
    call_twice(&mut g, x)
}

fn main() {}
