//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `t.0` is moved out of `t`, so the `&mut` it holds is resolved once, when `y`'s copy of it is
// written and dropped. Dropping `t` after the move must not resolve it a second time with the
// value it had at the move: `a` is 5 at the assertion.

fn main() {
    let mut a = 0;
    let t = (Some(&mut a), 1);
    let y = t.0;
    if let Some(r) = y {
        *r = 5;
    }
    assert!(a == 0);
}
