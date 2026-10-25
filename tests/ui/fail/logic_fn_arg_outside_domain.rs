//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `big` at `u64` is the identity, which has the result's facts wherever `n` has those of `usize`,
// and the generic `mk` applies it at `n - 1`, outside them. A logic function's value there is a
// fixed value of its result type, so the caller's `>= 0` of the result holds and does not make
// `assert!(x == 1)` vacuous.
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
        n
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == T::big(t, n - 1))]
fn mk<T: Mk>(t: T, n: usize) -> Ghost<T>
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
    thrust_macros::ghost!(|t: T, n: usize| -> T { T::big(t, n - 1) })
}

#[thrust::callable]
fn f(e: u64, x: usize) {
    if x == 0 {
        let g = mk(e, x);
        assert!(x == 1);
    }
}

fn main() {}
