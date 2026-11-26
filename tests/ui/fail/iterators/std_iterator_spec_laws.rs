//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_NO_INJECT_STD=1 THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// std.rs specializes its spec impls, so a crate compiling it as a source file enables
// `specialization` itself.
#![feature(specialization)]
#![allow(incomplete_features)]

// The bodies of the injected std.rs are not analyzed in the crates it is injected into. Compiled
// here as an ordinary source file, its bodies are checked: each `IteratorSpec` impl proves
// `produces_refl` and `produces_trans`, and each `DoubleEndedIteratorSpec` impl `produces_back_refl`
// and `produces_back_trans`, with an empty body, except the `produces_trans` of `Filter` and
// `Chain`, which call the lemmas of their witnesses and their cases.
// Fail twin: one more impl, whose `produces` bounds the end state even when nothing is produced
// but whose `inv` does not imply that bound, so `produces_refl` does not hold.
use thrust_models::{forall, Model, model::{Int, Seq}};
include!("../../../../std.rs");

#[derive(PartialEq)]
struct Countdown {
    n: i64,
}

impl Model for Countdown {
    type Ty = Countdown;
}

impl Iterator for Countdown {
    type Item = i64;

    #[thrust::trusted]
    #[thrust::callable]
    fn next(&mut self) -> Option<i64> {
        unimplemented!()
    }
}

#[thrust_macros::context]
impl IteratorSpec for Countdown {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<i64>, o: Self) -> bool {
        o.n <= self.n
            && 0 <= o.n
            && visited.len() == self.n - o.n
            && forall(|i: Int|
                !(0 <= i && i < visited.len()) || visited[i] == self.n - i)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).n <= 0 && *self == !self
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: Seq<<Self::Item as Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as Model>::Ty>,
        c: &Self,
    ) {
    }
}

fn main() {}
