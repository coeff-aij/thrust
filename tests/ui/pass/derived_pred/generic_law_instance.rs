//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_PER_INSTANCE_GENERICS=1

// Verifies. `Wrap<T>` leaves the derived `produces` out, so each instance of the impl has one of
// its own, and the inherited law `only_zero` is checked at the instance `Wrap<bool>` that `main`
// uses. There `next` yields only 0, which the law allows.

#[thrust_macros::context]
trait Iter {
    #[thrust_macros::predicate(derived)]
    fn produces(self, item: isize) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::produces(*a, x) ==> x == 0)]
    fn only_zero(a: &Self, x: isize) {}

    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<isize>;
}

// Yields 0 whatever `T` is.
struct Wrap<T> {
    v: T,
    n: isize,
}

impl<T: thrust_models::Model> thrust_models::Model for Wrap<T> {
    type Ty = (T::Ty, isize);
}

#[thrust_macros::context]
impl<T: thrust_models::Model> Iter for Wrap<T> {
    fn next(&mut self) -> Option<isize> {
        Some(0)
    }
}

fn main() {
    let mut w = Wrap { v: true, n: 0 };
    let x = w.next();
}
