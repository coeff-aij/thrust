//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trait's logic function at `u64`: a generic function verified once makes a ghost value from
// it, and a caller assumes the facts of the result's type, `>= 0` with `THRUST_INT_RANGE` unset.
// The definition is checked against them: here its value is `-1` at `n = 0` (model arithmetic is
// unbounded), and the expected error is that check.
use thrust_models::{Ghost, Model};

#[thrust_macros::context]
trait Mk: Model
where
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
{
    #[thrust_macros::logic]
    fn big(self, n: usize) -> Self;
}

#[thrust_macros::context]
impl Mk for u64 {
    #[thrust_macros::logic]
    fn big(self, n: usize) -> u64 {
        n - 1
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == T::big(t, n))]
fn mk<T: Mk>(t: T, n: usize) -> Ghost<T>
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
    thrust_macros::ghost!(|t: T, n: usize| -> T { T::big(t, n) })
}

#[thrust::callable]
fn f(e: u64, x: usize) {
    if x == 0 {
        let g = mk(e, x);
        assert!(x == 0);
    }
}

fn main() {}
