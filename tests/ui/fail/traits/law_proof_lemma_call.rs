//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A law's proof calls a lemma that uses the law at the lemma's type parameter. Called at the
// blanket impl's self type, the lemma uses the law being proved, as the direct call of
// `fail/traits/law_proof_self_call.rs` does. Accepting it would prove the law, which does not
// hold of `i64`, and `f(&1i64, &2i64)` would verify and panic.

use thrust_models::Model;

#[thrust_macros::context]
trait Tagged
where
    Self: Model,
{
    #[thrust_macros::predicate]
    fn small(self) -> bool {
        true
    }

    #[thrust_macros::law]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(Self::small(*a) && *a == *b)]
    fn all_small(a: &Self, b: &Self) {}
}

trait Base {}

impl Base for i64 {}

#[derive(PartialEq)]
struct Wrap<T>(T);

impl<T: Model> Model for Wrap<T> {
    type Ty = Wrap<T::Ty>;
}

#[thrust_macros::lemma]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(T::small(*a) && *a == *b)]
fn helper<T: Tagged>(a: &T, b: &T) {
    <T as Tagged>::all_small(a, b)
}

#[thrust_macros::context]
impl<T: Base + Model> Tagged for T {
    fn all_small(a: &T, b: &T) {
        helper::<T>(a, b) //~ ERROR: a law's proof uses a law only at a type parameter strictly inside the impl's self type
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(T::small(*a))]
#[thrust_macros::ensures(true)]
fn f<T: Tagged + PartialEq>(a: &T, b: &T) {
    assert!(*a == *b);
}

fn main() {}
