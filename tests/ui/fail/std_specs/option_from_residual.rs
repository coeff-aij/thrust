//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off --cfg thrust_std_conformance
//@rustc-env: THRUST_NO_INJECT_STD=1 THRUST_TRY_SPECS=1 THRUST_VERIFY_ONLY=std_transcriptions::** THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Fail twin of `tests/ui/pass/std_specs/option.rs`: `from_residual` has no other value
// to return than `None`, so its body panics instead, which its spec (`requires(true)`) does not
// allow.

include!("../../../../std.rs");
include!("../../../../std_try.rs");

mod std_transcriptions {
    use crate::thrust_models;
    use std::convert::Infallible;
    use std::ops::ControlFlow;

    // library/core/src/option.rs, `impl<T: [const] PartialEq> const PartialEq for Option<T>`, `fn eq(&self, other: &Self) -> bool`
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

    // library/core/src/option.rs, `impl<T> const ops::Try for Option<T>`, `fn branch(self) -> ControlFlow<Self::Residual, Self::Output>`
    pub fn option_branch<T>(opt: Option<T>) -> ControlFlow<Option<Infallible>, T> {
        match opt {
            Some(v) => ControlFlow::Continue(v),
            None => ControlFlow::Break(None),
        }
    }

    // library/core/src/option.rs, `impl<T> const ops::FromResidual<Option<convert::Infallible>> for Option<T>`, `fn from_residual(residual: Option<convert::Infallible>) -> Self`
    pub fn option_from_residual<T>(residual: Option<Infallible>) -> Option<T> {
        match residual {
            None => panic!(),
        }
    }
}

fn main() {}
