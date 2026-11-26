//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The macro binds `mut $x` from the caller's identifier `x`; the annotation's `x` is the inner one
// (0), so the assume! holds and assert!(false) must fail.
macro_rules! rebind {
    ($x:ident, $s:stmt) => {{
        let mut $x: i64 = 0;
        $x += 0;
        $s;
        let _ = $x;
    }};
}

fn main() {
    let x: i64 = 5;
    rebind!(x, thrust_macros::assume!(|x: i64| x == 0));
    let _ = x;
    assert!(false);
}
