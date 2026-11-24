//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::{exists, forall, model::{Closure, Mut}};

// An `FnMut` parameter instantiated with a shared reference to an `Fn` closure that owns a
// `&mut`, and handed to a function that calls it by value.
#[thrust_macros::requires(thrust_macros::pre!(g()))]
#[thrust_macros::ensures(thrust_macros::post!(g(), result))]
fn call_once<G: FnOnce() -> i64>(g: G) -> i64 {
    g()
}

#[thrust_macros::requires(forall(|c: Closure<F>| thrust_macros::pre!(c())))]
#[thrust_macros::ensures(exists(|h| thrust_macros::post!(Mut::new(f, h)(), result)))]
fn consume<F: FnMut() -> i64>(f: F) -> i64 {
    call_once(f)
}

fn main() {
    let mut n: i64 = 1;
    let r = &mut n;
    let c = move || *r;
    let a = consume(&c);
    assert!(a == 1);
}
