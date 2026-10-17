//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A blanket impl's self type is a type parameter, and its proof of a law calls the law it proves
// when it calls the law at that parameter: the call is rejected as at `Self`. Accepting it would
// prove the law below, which does not hold of `i64`, and `f` would verify.

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

#[thrust_macros::context]
impl<T: Base + Model> Tagged for T {
    fn all_small(a: &T, b: &T) {
        <T as Tagged>::all_small(a, b) //~ ERROR: a lemma or a law's proof calls only lemmas, logic functions, predicates, model operations and laws at a type parameter
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(T::small(*a))]
#[thrust_macros::ensures(true)]
fn f<T: Tagged + PartialEq>(a: &T, b: &T) {
    assert!(*a == *b);
}

fn main() {
    f(&1i64, &2i64);
}
