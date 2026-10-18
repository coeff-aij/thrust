//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trait's default proof of a law uses the law at a trait parameter. An impl that sets the
// parameter to its self type inherits a proof that uses the law it proves, so the default body is
// checked at each impl that inherits it. Accepting it would prove `tag` of every `S`, and
// `f(&S(0))` would verify and panic.

use thrust_models::Model;

#[thrust_macros::context]
trait Tr<U: Tr<U>>
where
    Self: Model,
{
    #[thrust_macros::predicate]
    fn tag(self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(U::tag(*b))]
    fn l(a: &Self, b: &U) {
        <U as Tr<U>>::l(b, b) //~ ERROR: a law's proof uses a law only at a type parameter strictly inside the impl's self type
    }
}

#[derive(PartialEq)]
struct S(i64);

impl Model for S {
    type Ty = S;
}

#[derive(PartialEq)]
struct Wrap<T>(T);

impl<T: Model> Model for Wrap<T> {
    type Ty = Wrap<T::Ty>;
}

#[thrust_macros::context]
impl Tr<S> for S {
    #[thrust_macros::predicate]
    fn tag(self) -> bool {
        false
    }
}

fn main() {}
