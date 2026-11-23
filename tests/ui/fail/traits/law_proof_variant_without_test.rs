//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables

// A law is assumed of every value of its parameters' sorts, where `Ok((0, ()))` and `Err((0, ()))`
// are values. rustc reads either variant's field without a test, since neither has values, so in
// the proof each read is an obligation that the value is of that variant, and reading both does
// not prove the false `tag`.
use std::convert::Infallible;
use thrust_models::Model;

#[thrust_macros::context]
trait Absurd
where
    Self: Model,
{
    #[thrust_macros::predicate]
    fn tag(self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::tag(*a))]
    fn absurd(a: &Self, r: Result<(i64, Infallible), (i64, Infallible)>);
}

struct S(i64);

impl Model for S {
    type Ty = S;
}

#[thrust_macros::context]
impl Absurd for S {
    #[thrust_macros::predicate]
    fn tag(self) -> bool {
        false
    }

    fn absurd(a: &S, r: Result<(i64, Infallible), (i64, Infallible)>) {
        let Ok((n, _)) = r;
        let Err((m, _)) = r;
    }
}

fn main() {}
