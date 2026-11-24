//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::{forall, model::Closure};

// A function whose `Fn` parameter is a shared reference hands it to one that calls it by value:
// the call consumes the reference, not the closure it points to.
#[thrust_macros::requires(thrust_macros::pre!(g()))]
#[thrust_macros::ensures(thrust_macros::post!(g(), result))]
fn call_once<G: FnOnce() -> i64>(g: G) -> i64 {
    g()
}

#[thrust_macros::requires(forall(|c: Closure<H>| thrust_macros::pre!(c())))]
fn wrap<H: Fn() -> i64>(h: &H) -> i64 {
    call_once(h)
}

fn main() {
    let mut n: i64 = 1;
    let r = &mut n;
    let c = move || *r;
    let _ = wrap(&c);
}
