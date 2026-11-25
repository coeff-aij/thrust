//@error-in-other-file: Unsat
//@compile-flags: -Aunused_parens -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
use thrust_models::{Model, model::Closure};
struct S<F> {
    func: F,
}

impl<F> Model for S<F> {
    type Ty = S<Closure<F>>;
}

#[thrust_macros::context]
impl<F: Fn(i64) -> i64> S<F> {
    #[thrust_macros::requires(thrust_macros::pre!(((*self).func)(v)))]
    #[thrust_macros::ensures(thrust_macros::post!(((*self).func)(v), result))]
    fn call(&self, v: i64) -> i64 {
        (self.func)(v) + 1
    }
}

fn main() {}
