//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/traits/law_proof_variant_aggregate.rs`: the code that builds `Never::X`, which
// has no values, is under `k < 0`, which the law's precondition makes unreachable in the logic, so
// the proof verifies.

use std::convert::Infallible;
use thrust_models::Model;

enum Never {
    X(Infallible),
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
    fn absurd(a: &Self, i: &Infallible, k: i64);
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

    fn absurd(a: &S, i: &Infallible, k: i64) {
        if k < 0 {
            let _n = Never::X(*i);
        }
    }
}

fn main() {}
