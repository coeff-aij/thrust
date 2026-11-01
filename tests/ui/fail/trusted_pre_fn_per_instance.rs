//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The twin of `pass/trusted_pre_fn_per_instance.rs`: `t`'s `requires` states `pre!(g(x))` at
// `T = i32` only. The call `t(true, 0)` discharges nothing of `g`, so `g` must accept every
// argument there, whatever the call at `i32` states.
use thrust_models::Model;

fn g(x: i32) {
    assert!(x > 0)
}

#[thrust_macros::context]
trait Guard
where
    Self: Model,
{
    #[thrust_macros::predicate]
    fn allows(self, x: i32) -> bool;
}

impl Guard for i32 {
    #[thrust_macros::predicate]
    fn allows(self, x: i32) -> bool {
        thrust_macros::pre!(g(x))
    }
}

impl Guard for bool {
    #[thrust_macros::predicate]
    fn allows(self, x: i32) -> bool {
        true
    }
}

#[thrust::trusted]
#[thrust_macros::requires(T::allows(t, x))]
#[thrust_macros::ensures(true)]
fn t<T: Guard>(t: T, x: i32) {
    g(x)
}

fn main() {
    t(1i32, 1);
    t(true, 0);
}
