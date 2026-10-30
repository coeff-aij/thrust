//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `requires` that also calls a trait's predicate at a type parameter, whose body is the impl's
// and not known where the `pre!` are collected: the `pre!` written beside it still counts as stated.

use thrust_models::Model;

#[thrust_macros::context]
trait Positive
where
    Self: Model,
{
    #[thrust_macros::predicate]
    fn ok(self) -> bool;
}

impl Positive for i32 {
    #[thrust_macros::predicate]
    fn ok(self) -> bool {
        self > 0
    }
}

#[thrust::trusted]
#[thrust_macros::requires(T::ok(t) && thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn apply_pre<T: Positive, F: Fn(i32)>(t: T, f: F, x: i32) {
    f(x)
}

fn main() {
    apply_pre(1, |x: i32| assert!(x > 0), 1);
}
