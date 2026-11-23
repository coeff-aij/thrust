//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trait method's contract means at the impl's instance (`Out = Infallible`) what it means over
// the trait's types, where a caller generic over the trait reads it: `W<X::Out>` keeps `B`.
use std::convert::Infallible;
use thrust_models::forall;

enum W<T> {
    A(i64),
    B(T),
}

#[thrust_macros::context]
trait Tr {
    type Out;
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(forall(|w: W<Self::Out>| match w { W::A(_) => true, W::B(_) => true }))]
    fn m(&self);
}

struct S;

#[thrust_macros::context]
impl Tr for S {
    type Out = Infallible;
    fn m(&self) {}
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn h<X: Tr>(x: &X) {
    x.m();
}

fn main() {
    h(&S);
}
