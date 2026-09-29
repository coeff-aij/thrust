//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_NO_INJECT_STD=1 THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 COAR_IMAGE=coar:0360cb142

// The bodies of the injected std.rs are not analyzed in the crates it is injected into. Compiled
// here as an ordinary source file, its bodies are checked: each `IteratorSpec` impl proves
// `produces_refl` and `produces_trans` with an empty body.
// On fptprove 2493045c3 the `produces_trans` of `Enumerate` and `Zip` time out: their `produces`
// states the inner iterators' history under an existential, whose witness that build does not find.

include!("../../../../std.rs");

fn main() {}
