//@compile-flags: -Adead_code -Aunused -C debug-assertions=false

// The `&mut` can come through `Self`: a law taking `a: Self` in an impl for `&mut i64` could
// write through `a`, so the impl is rejected although the trait names no `&mut`.

use thrust_models::Model;

#[thrust_macros::context]
trait P: Model + Sized {
    #[thrust_macros::predicate]
    fn p(self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::p(a))]
    fn l(a: Self);
}

#[thrust_macros::context]
impl<'x> P for &'x mut i64 {
    #[thrust_macros::predicate]
    fn p(self) -> bool {
        !self == 7
    }

    fn l(a: &'x mut i64) { //~ ERROR: a law cannot take or return a `&mut`
        *a = 7;
    }
}

fn main() {}
