//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::{forall, model::Closure};

// At a closure type parameter `hist_inv!` is known only through its laws, which do not make it
// symmetric.
#[thrust_macros::requires(forall(|c: Closure<F>| thrust_macros::pre!(c())))]
#[thrust_macros::ensures(thrust_macros::hist_inv!(!f, *f))]
fn call_twice<F: FnMut()>(f: &mut F, n: i64) {
    if n > 0 {
        f();
        f();
    }
}

fn main() {}
