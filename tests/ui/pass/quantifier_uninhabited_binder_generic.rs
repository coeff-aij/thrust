//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A generic item's contract means at an instance what it means over its type parameters, where it
// is verified: `W<T>` has `B` values whatever `T`, also at `g::<Infallible>`, so the call cannot
// establish a precondition that only the instance would make true.
use std::convert::Infallible;
use thrust_models::forall;

enum W<T> {
    A(i64),
    B(T),
}

#[thrust_macros::requires(forall(|w: W<T>| match w { W::A(_) => true, W::B(_) => true }))]
#[thrust_macros::ensures(true)]
fn g<T>() {
    assert!(true);
}

fn main() {
    g::<Infallible>();
}
