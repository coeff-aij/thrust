//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=main,g
// The twin of `fail/verify_only/uncontracted_under_unselected.rs`: `t` without a contract is
// analyzed, and its call gives `g` its precondition.

fn g(x: i32) {
    assert!(x > 0);
}

fn t() {
    g(1)
}

fn main() {
    t()
}
