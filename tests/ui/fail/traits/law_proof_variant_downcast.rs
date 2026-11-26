//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `NeverP::X` has no values, so its enum's datatype has no constructor for it, and code that reads
// its field does not run. The law is assumed of every value of the sorts, which are never empty, so
// the proof must show that point unreachable in the logic, as it must a block rustc ends in
// `Unreachable`; here it is reached where `k > 0`.

use std::convert::Infallible;
use thrust_models::Model;

struct Pair(Infallible, i64);

enum NeverP {
    X(Pair),
}

impl Model for NeverP {
    type Ty = NeverP;
}

#[thrust_macros::context]
trait Absurd
where
    Self: Model,
{
    #[thrust_macros::predicate]
    fn tag(self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(k > 0)]
    #[thrust_macros::ensures(Self::tag(*a))]
    fn absurd(a: &Self, n: &NeverP, k: i64);
}

struct S(i64);

impl Model for S {
    type Ty = S;
}

#[thrust_macros::context]
impl Absurd for S {
    #[thrust_macros::predicate]
    fn tag(self) -> bool {
        true
    }

    fn absurd(a: &S, n: &NeverP, k: i64) {
        if k > 0 {
            let NeverP::X(p) = n;
            let _y = p.1;
        }
    }
}

fn main() {}
