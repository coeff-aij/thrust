//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_NO_INJECT_STD=1 THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120

// The bodies of the injected std.rs are not analyzed in the crates it is injected into. Compiled
// here as an ordinary source file, its bodies are checked: each `IteratorSpec` impl proves
// `produces_refl` and `produces_trans`, and each `DoubleEndedIteratorSpec` impl `produces_back_refl`
// and `produces_back_trans`, with an empty body, except the `produces_trans` of `Filter` and
// `Chain`, which are trusted (std.rs says why).

include!("../../../../std.rs");

fn main() {}
