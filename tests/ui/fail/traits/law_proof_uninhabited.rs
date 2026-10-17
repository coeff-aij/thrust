//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `S` has no value, so `match a.0 {}` ends the proof in `Unreachable`. The law is assumed of every
// value of `T`'s sort, which is never empty, so a proof must show such a block unreachable in the
// logic. Accepting it would prove `false` of every `T: Absurd`, and `f` would verify, though
// `f::<S>` panics.

#![feature(never_type)]

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
    #[thrust_macros::ensures(false)]
    fn absurd(a: &Self);
}

struct S(!);

impl Model for S {
    type Ty = S;
}

#[thrust_macros::context]
impl Absurd for S {
    #[thrust_macros::predicate]
    fn tag(self) -> bool {
        true
    }

    fn absurd(a: &S) {
        match a.0 {}
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(exists(|y| T::tag(y)))]
#[thrust_macros::ensures(true)]
fn f<T: Absurd>(n: i64) {
    assert!(false);
}

fn main() {
    f::<S>(0);
}
