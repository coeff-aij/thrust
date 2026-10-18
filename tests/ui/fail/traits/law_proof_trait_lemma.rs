//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A law's proof calls a trait's lemma, which resolves to `X`'s, and that uses the law at its type
// parameter. Called at the blanket impl's self type, it uses the law being proved, as the lemma of
// `fail/traits/law_proof_lemma_call.rs` does.

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

#[thrust_macros::context]
trait Helper {
    #[thrust_macros::lemma]
    #[thrust_macros::requires(false)]
    #[thrust_macros::ensures(U::small(*a) && *a == *b)]
    fn h<U: Tagged>(a: &U, b: &U) {}
}

struct X;

#[thrust_macros::context]
impl Helper for X {
    #[thrust_macros::lemma]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(U::small(*a) && *a == *b)]
    fn h<U: Tagged>(a: &U, b: &U) {
        <U as Tagged>::all_small(a, b)
    }
}

#[thrust_macros::context]
impl<T: Base + Model> Tagged for T {
    fn all_small(a: &T, b: &T) {
        <X as Helper>::h::<T>(a, b) //~ ERROR: a law's proof uses a law only at a type parameter strictly inside the impl's self type
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(T::small(*a))]
#[thrust_macros::ensures(true)]
fn f<T: Tagged + PartialEq>(a: &T, b: &T) {
    assert!(*a == *b);
}

fn main() {}
