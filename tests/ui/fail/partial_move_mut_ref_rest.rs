//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Dropping `t` after `t.0` is moved out resolves the `&mut` left in `t.1` to the value `b` keeps:
// `b` is 0 at the assertion.

fn main() {
    let mut a = 0;
    let mut b = 0;
    let t = (Some(&mut a), Some(&mut b));
    let y = t.0;
    if let Some(r) = y {
        *r = 5;
    }
    assert!(a == 5);
    assert!(b == 1);
}
