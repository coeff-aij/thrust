//@check-pass
//@compile-flags: -C debug-assertions=off
// A `proof_assert!` in a closure's body names a reference the body copies from a capture with
// `let`, which the MIR keeps only as the copy made for a deref.
fn main() {
    let x = 5i64;
    let r: &i64 = &x;
    let rr: &&i64 = &r;
    let mut calls = 0i64;
    let mut f = || {
        calls += 1;
        let k: &i64 = rr;
        thrust_macros::proof_assert!(|k: &i64| *k == 5);
        *k
    };
    f();
}
