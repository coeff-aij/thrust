//@error-in-other-file: Unsat
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

// `closure_hist_inv_clause_generic.rs` without its `hist_inv` clause: `g`'s relation through the
// `f` it owns is left to inference.
// The postcondition claims the result is that of a call at `f`'s initial state with `x`, which no
// closure contract implies.
#[thrust_macros::context]
#[thrust_macros::requires(forall(|c: Closure<F>, y: i64| thrust_macros::pre!(c(y))))]
#[thrust_macros::ensures(exists(|d: Closure<F>| thrust_macros::post!(Mut::new(f, d)(x), result)))]
fn call_twice_through<F: FnMut(i64) -> i64>(mut f: F, x: i64) -> i64 {
    let mut g = thrust_macros::closure!(
        captures(f: &mut F),
        move |y: i64| -> i64 { f(y) },
    );
    call_twice(&mut g, x)
}

fn main() {}
