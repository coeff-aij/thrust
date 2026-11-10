//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 THRUST_PER_INSTANCE_GENERICS=1

// Verifies: the specialized `next` yields 0 as well, which the law allows.
// `Wrap<T>` leaves the derived `produces` out, so its laws are checked at each instance
// (`derived_pred/generic_law_instance.rs`). The impl for every `Wrap<T>` proves `only_zero`, and
// the one specialized where `T: Fast` takes that proof and overrides `next`: the proof is checked
// at `Wrap<i32>` against the base impl's `produces` and at `Wrap<u8>` against the specialized
// impl's.
trait Fast: thrust_models::Model {}

impl Fast for u8 {}

#[thrust_macros::context]
trait Iter {
    #[thrust_macros::predicate(derived)]
    fn produces(self, item: isize) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::produces(*a, x) ==> x == 0)]
    fn only_zero(a: &Self, x: isize);

    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<isize>;
}

struct Wrap<T> {
    v: T,
    n: isize,
}

impl<T: thrust_models::Model> thrust_models::Model for Wrap<T> {
    type Ty = (T::Ty, isize);
}

#[thrust_macros::context]
impl<T: thrust_models::Model> Iter for Wrap<T> {
    default fn next(&mut self) -> Option<isize> {
        Some(0)
    }

    fn only_zero(a: &Self, x: isize) {}
}

#[thrust_macros::context]
impl<T: Fast> Iter for Wrap<T> {
    fn next(&mut self) -> Option<isize> {
        Some(0)
    }
}

fn main() {
    let mut w = Wrap { v: 0u8, n: 0 };
    let x = w.next();
    let mut v = Wrap { v: 0i32, n: 0 };
    let y = v.next();
}
