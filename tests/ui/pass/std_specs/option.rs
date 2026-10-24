//@check-pass
//@compile-flags: -C debug-assertions=off --cfg thrust_std_conformance
//@rustc-env: THRUST_NO_INJECT_STD=1 THRUST_TRY_SPECS=1 THRUST_VERIFY_ONLY=std_transcriptions::** THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The specs of `Option`'s methods in `std.rs` and `std_try.rs` whose std bodies are safe code,
// checked against those bodies: under `cfg(thrust_std_conformance)` each spec's target is the
// transcription below, a local function whose body Thrust checks against the spec. The query has
// forall sorts (the transcriptions are generic), so it needs PCSat; z3 does not read it.
//
// Each `// std:` line names the std function a transcription copies: its file in the toolchain's
// `rust-src`, its impl's header and its signature. `tests/std_transcriptions.rs` finds that
// function and checks that the body below is its body, with the parameters named as the spec
// names them. The `eq` spec reads the payloads' `==` through the `PartialEq` spec of `std.rs` at
// the `ModelEq` bound, so this check is relative to that spec.

include!("../../../../std.rs");
include!("../../../../std_try.rs");

mod std_transcriptions {
    use crate::thrust_models;
    use std::convert::Infallible;
    use std::ops::ControlFlow;

    // std: library/core/src/option.rs, `impl<T: [const] PartialEq> const PartialEq for Option<T>`, `fn eq(&self, other: &Self) -> bool`
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

    // std: library/core/src/option.rs, `impl<T> const ops::Try for Option<T>`, `fn branch(self) -> ControlFlow<Self::Residual, Self::Output>`
    pub fn option_branch<T>(opt: Option<T>) -> ControlFlow<Option<Infallible>, T> {
        match opt {
            Some(v) => ControlFlow::Continue(v),
            None => ControlFlow::Break(None),
        }
    }

    // std: library/core/src/option.rs, `impl<T> const ops::FromResidual<Option<convert::Infallible>> for Option<T>`, `fn from_residual(residual: Option<convert::Infallible>) -> Self`
    pub fn option_from_residual<T>(residual: Option<Infallible>) -> Option<T> {
        match residual {
            None => None,
        }
    }
}

fn main() {}
