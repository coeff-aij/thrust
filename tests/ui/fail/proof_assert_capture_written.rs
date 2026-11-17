//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// A `proof_assert!` in an `FnMut` closure's body names a captured variable the closure has just
// written.
fn main() {
    let mut n = 0i64;
    let mut inc = || {
        n += 1;
        thrust_macros::proof_assert!(|n: i64| n == 0);
    };
    inc();
}
