//@check-pass
//@compile-flags: -Adead_code -Aunused -C debug-assertions=false
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A law may take a `&mut` behind a shared reference: with `Self = &mut i64`, `a: &Self` is
// read only, so its proof cannot choose the final value and holds for every one.

use thrust_models::Model;

#[thrust_macros::context]
trait P: Model + Sized {
    #[thrust_macros::predicate]
    fn p(self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::p(*a) == Self::p(*a))]
    fn l(a: &Self);
}

#[thrust_macros::context]
impl<'x> P for &'x mut i64 {
    #[thrust_macros::predicate]
    fn p(self) -> bool {
        !self == 7
    }

    fn l(a: &&'x mut i64) {}
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(T::p(*x) == T::p(*x))]
fn use_p<T: P>(x: &T) {}

fn main() {
    let mut v = 0i64;
    use_p(&&mut v);
}
