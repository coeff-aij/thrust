//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// A variable a quantifier binds at an enum type does not range over a variant whose payload has no
// value at the instance, though the definition gives it values: `Result<i64, Infallible>`'s
// `Err` and `W<Infallible>`'s `B`, whose models are `Err(())` and `B(())`.
use std::convert::Infallible;
use thrust_models::forall;

enum W<T> {
    A(i64),
    B(T),
}

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|r: Result<i64, Infallible>| match r { Ok(_) => true })
        && forall(|w: W<Infallible>| match w { W::A(_) => true }));
    assert!(x == 0);
}
