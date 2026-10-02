//@ignore-on-host: not yet verifiable, the frontend panics on `&mut F` passed as an `FnMut` (see ../../pass/unnest_infer/README.md)
//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::{exists, forall, model::{Closure, Mut}};

// `call_twice` takes its closure by value, as std's `find` does, and hides the state between the
// calls behind `unnest!`.
#[thrust_macros::requires(forall(|c: Closure<G>, y: i64| thrust_macros::pre!(c(y))))]
#[thrust_macros::ensures(exists(|c: Closure<G>, d: Closure<G>, y: i64|
    thrust_macros::unnest!(g, c) && thrust_macros::post!(Mut::new(c, d)(y), result)))]
fn call_twice<G: FnMut(i64) -> i64>(mut g: G, x: i64) -> i64 {
    let a = g(x);
    g(a)
}

// `Filter::next` calls `self.iter.find(&mut self.predicate)`: the callee's closure is `&mut F`,
// itself an `FnMut`, whose calls are calls of `f`. The relation over `&mut F`'s states that
// `call_twice` states has to be read back as one over `f`'s. The postcondition claims the result
// is that of a call at `f`'s initial state with `x`, which no closure contract implies.
#[thrust_macros::context]
#[thrust_macros::requires(forall(|c: Closure<F>, y: i64| thrust_macros::pre!(c(y))))]
#[thrust_macros::ensures(exists(|d: Closure<F>| thrust_macros::post!(Mut::new(*f, d)(x), result)))]
fn call_twice_by_ref<F: FnMut(i64) -> i64>(f: &mut F, x: i64) -> i64 {
    call_twice(&mut *f, x)
}

fn main() {}
