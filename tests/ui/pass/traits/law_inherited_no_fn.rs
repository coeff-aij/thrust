//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An impl that defines no function inherits the trait's laws, and they are checked at it as at
// any other impl, since a generic caller assumes them.

use thrust_models::Model;

#[thrust_macros::context]
trait Tagged
where
    Self: Model,
{
    #[thrust_macros::predicate]
    fn small(self) -> bool {
        true
    }

    #[thrust_macros::law]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(Self::small(*a))]
    fn all_small(a: &Self) {}
}

impl Tagged for i64 {}

#[thrust_macros::context]
#[thrust_macros::requires(T::small(*a))]
#[thrust_macros::ensures(true)]
fn f<T: Tagged>(a: &T) {
    T::all_small(a);
}

fn main() {
    f(&1i64);
}
