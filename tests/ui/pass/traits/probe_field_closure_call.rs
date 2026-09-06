// FIXME: Unsat; FnMut closure pre!/post! specs are Unsat branch-wide (closure_postcondition_fnmut.rs fails too).
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

// Probe: calling a closure stored in a struct field, with pre!/post! on the field (the Map pattern).
use thrust_models::{exists, model::Mut};

struct S<F> {
    func: F,
}

// The field must be modelled as `model::Closure<F>` for `pre!`/`post!` to accept it as a receiver.
impl<F> thrust_models::Model for S<F> {
    type Ty = S<thrust_models::model::Closure<F>>;
}

#[thrust_macros::context]
impl<F: FnMut(i64) -> i64> S<F> {
    #[thrust_macros::requires(exists(|g| thrust_macros::pre!(Mut::new((*self).func, g)(v))))]
    #[thrust_macros::ensures(thrust_macros::post!(Mut::new((*self).func, (!self).func)(v), result))]
    fn call(&mut self, v: i64) -> i64 {
        (self.func)(v)
    }
}

fn main() {}
