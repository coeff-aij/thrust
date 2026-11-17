//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// A `proof_assert!` names a `&mut` reborrowed from a `&mut` capture, written through it.
fn main() {
    let mut x = 5i64;
    let m: &mut i64 = &mut x;
    let mut f = || {
        let k: &mut i64 = m;
        *k += 1;
        thrust_macros::proof_assert!(|k: &mut i64| *k == 7);
    };
    f();
}
