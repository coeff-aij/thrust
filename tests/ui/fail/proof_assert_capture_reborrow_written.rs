//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// A `proof_assert!` names a reference copied from a capture after the closure has assigned the
// captured variable: the name stands for the copy, not for the variable's new value.
fn main() {
    let x = 5i64;
    let y = 6i64;
    let ry: &i64 = &y;
    let mut r: &i64 = &x;
    let mut f = || {
        let k: &i64 = r;
        r = ry;
        thrust_macros::proof_assert!(|k: &i64| *k == 6);
    };
    f();
}
