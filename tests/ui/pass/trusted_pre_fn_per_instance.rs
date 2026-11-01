//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A function's `pre!` that a trusted function's `requires` states through a trait predicate
// counts at the instance whose predicate states it: `t::<i32>` states `pre!(g(x))`, which the
// call discharges, so `g` need not accept other arguments.
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
}
