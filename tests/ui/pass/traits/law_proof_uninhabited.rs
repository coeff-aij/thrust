//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/traits/law_proof_uninhabited.rs`: the `otherwise` arm of an exhaustive match,
// which rustc ends in `Unreachable`, is unreachable in the logic too, so the proof verifies.

use thrust_models::exists;
use thrust_models::Model;

#[thrust_macros::context]
trait Absurd
where
    Self: Model,
{
    #[thrust_macros::predicate]
    fn tag(self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(Self::tag(*a))]
    fn absurd(a: &Self);
}

enum E {
    A,
    B,
}

struct S(E);

impl Model for S {
    type Ty = S;
}

#[thrust_macros::lemma]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn at_a() {}

#[thrust_macros::lemma]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn at_b() {}

#[thrust_macros::context]
impl Absurd for S {
    #[thrust_macros::predicate]
    fn tag(self) -> bool {
        true
    }

    fn absurd(a: &S) {
        match a.0 {
            E::A => at_a(),
            E::B => at_b(),
        }
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(exists(|y| T::tag(y)) && n == 0)]
#[thrust_macros::ensures(true)]
fn f<T: Absurd>(n: i64) {
    assert!(n == 0);
}

fn main() {
    f::<S>(0);
}
