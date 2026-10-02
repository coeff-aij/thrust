//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::{exists, forall, model::{Closure, Mut}};

// The closure owns its counter, so the relation its captures give says nothing of it; its
// `hist_inv` clause states that the counter never decreases. `call_twice` hides the state between
// the calls, so the caller bounds the second result only through that clause.
#[thrust_macros::requires(forall(|c: Closure<F>| thrust_macros::pre!(c())))]
#[thrust_macros::ensures(exists(|g|
    thrust_macros::hist_inv!(*f, g) && thrust_macros::post!(Mut::new(g, !f)(), result)))]
fn call_twice<F: FnMut() -> i64>(f: &mut F) -> i64 {
    f();
    f()
}

fn main() {
    let mut n: i64 = 0;
    let mut c = thrust_macros::closure!(
        captures(n: &mut i64),
        requires(true),
        ensures(!n == *n + 1 && result == !n),
        hist_inv(*n <= !n),
        move || -> i64 {
            n += 1;
            n
        },
    );
    let r = call_twice(&mut c);
    assert!(r >= 1);
}
