//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off --cfg thrust_std_conformance
//@rustc-env: THRUST_NO_INJECT_STD=1 THRUST_TRY_SPECS=1 THRUST_VERIFY_ONLY=std_transcriptions::** THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The specs of `Option`'s methods in `std.rs` and `std_try.rs` whose std bodies are safe code,
// checked against those bodies: under `cfg(thrust_std_conformance)` each spec's target is the
// transcription below, a local function whose body Thrust checks against the spec. Each body is
// std's at the line of the pinned toolchain's `rust-src` (rustc 12eb345e5) that its comment names,
// with the parameters named as the spec names them; thrust-research
// `scripts/check_std_transcriptions.py` compares the two.

include!("../../../../std.rs");
include!("../../../../std_try.rs");

mod std_transcriptions {
    use crate::thrust_models;
    use std::convert::Infallible;
    use std::ops::ControlFlow;

    // `<Option<T> as PartialEq>::eq`, library/core/src/option.rs:2350
    pub fn option_eq<T>(x: &Option<T>, y: &Option<T>) -> bool
    where
        T: thrust_models::Model + thrust_models::ModelEq + PartialEq,
    {
        match (x, y) {
            (Some(l), Some(r)) => *l == *r,
            (Some(_), None) => false,
            (None, Some(_)) => false,
            (None, None) => true,
        }
    }

    // `<Option<T> as Try>::branch`, library/core/src/option.rs:2651
    pub fn option_branch<T>(opt: Option<T>) -> ControlFlow<Option<Infallible>, T> {
        match opt {
            Some(_) => ControlFlow::Break(None),
            None => ControlFlow::Break(None),
        }
    }

    // `<Option<T> as FromResidual<Option<Infallible>>>::from_residual`, library/core/src/option.rs:2665
    pub fn option_from_residual<T>(residual: Option<Infallible>) -> Option<T> {
        match residual {
            None => None,
        }
    }
}

fn main() {}
