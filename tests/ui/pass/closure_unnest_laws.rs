//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::{forall, model::Closure};

// At a closure type parameter `unnest!` is known only through its laws: no call leaves it by
// reflexivity, each call by its postcondition, and two calls by transitivity.
#[thrust_macros::requires(forall(|c: Closure<F>| thrust_macros::pre!(c())))]
#[thrust_macros::ensures(thrust_macros::unnest!(*f, !f))]
fn call_twice<F: FnMut()>(f: &mut F, n: i64) {
    if n > 0 {
        f();
        f();
    }
}

fn main() {}
