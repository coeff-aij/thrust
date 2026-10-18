//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/traits/law_proof_default_body.rs`: a trait's default proof of a law uses the
// law at a trait parameter, which this impl sets to a type parameter inside its self type.

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
        <U as Tr<U>>::l(b, b)
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
impl<T: Tr<T>> Tr<T> for Wrap<T> {
    #[thrust_macros::predicate]
    fn tag(self) -> bool {
        true
    }
}

fn main() {}
