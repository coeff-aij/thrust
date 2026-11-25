//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::{forall, model::{Closure, Mut}};

// A closure's precondition survives a call: `post!` at the closure with the final state `f2` states
// `hist_inv!(f1, f2)`, which for an `Fn` closure is `f1 == f2`, so `pre!(f2(e))` follows from
// `pre!(f1(e))` as it does for a closure type parameter through `postcondition_mut_hist_inv`.
#[thrust_macros::requires(forall(|f1: Closure<F>, f2: Closure<F>, e: i64, b: i64|
    !(thrust_macros::hist_inv!(func, f1)
        && thrust_macros::pre!(f1(e))
        && thrust_macros::post!(Mut::new(f1, f2)(e), b))
        || thrust_macros::pre!(f2(e))))]
fn needs_precondition_preserved<F: FnMut(i64) -> i64>(func: F) {}

fn main() {
    let n: i64 = 5;
    let f = thrust_macros::closure!(
        captures(n: &i64),
        requires(x > *n),
        ensures(result == x),
        |x: i64| -> i64 { if x > n { x } else { x } },
    );
    needs_precondition_preserved(f);
}
