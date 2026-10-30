//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A trait predicate's default body states `pre!`, and the impl that runs overrides it with `true`.
// The `pre!` of the default does not count as stated, so the closure must accept every argument.

use thrust_models::Model;

#[thrust_macros::context]
trait Guard
where
    Self: Model,
{
    #[thrust_macros::predicate]
    fn allows<G: Fn(i32)>(self, g: G, x: i32) -> bool {
        thrust_macros::pre!(g(x))
    }
}

impl Guard for i32 {
    #[thrust_macros::predicate]
    fn allows<G: Fn(i32)>(self, g: G, x: i32) -> bool {
        true
    }
}

#[thrust::trusted]
#[thrust_macros::requires(T::allows(t, f, x))]
#[thrust_macros::ensures(true)]
fn apply_guarded<T: Guard, F: Fn(i32)>(t: T, f: F, x: i32) {
    f(x)
}

fn main() {
    apply_guarded(1, |x: i32| assert!(x > 0), 0);
}
