//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::Model;
#[thrust_macros::context]
trait Tr {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result > 0)]
    fn m<U>(&self, u: U) -> i32;
}

struct W<T>(T);

impl<T> Model for W<T>
where
    T: Model,
{
    type Ty = Self;
}

impl<T> Tr for W<T> {
    fn m<U>(&self, _u: U) -> i32 {
        1
    }
}

fn main() {
    let w = W(0i32);
    assert!(w.m(0i64) > 0);
}
