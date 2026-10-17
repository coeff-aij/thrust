//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/traits/law_proof_lemma_call.rs`: a lemma that uses the law at its type
// parameter serves the proof of an impl for a type that wraps it, called at the wrapped type.

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
impl<T: Tagged> Tagged for Wrap<T> {
    fn all_small(a: &Wrap<T>, b: &Wrap<T>) {
        helper::<T>(&a.0, &b.0)
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(T::small(*a))]
#[thrust_macros::ensures(true)]
fn f<T: Tagged + PartialEq>(a: &T, b: &T) {
    assert!(*a == *b);
}

fn main() {}
