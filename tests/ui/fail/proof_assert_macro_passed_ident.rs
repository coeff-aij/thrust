//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The macro binds `$x` (0) and assumes of it `$x == 0`, which holds; the caller's `x` is 5.
macro_rules! bind_and_assume {
    ($x:ident) => {{
        let $x: i64 = 0;
        thrust_macros::assume!(|$x: i64| $x == 0);
        let _ = $x;
    }};
}

fn main() {
    let x: i64 = 5;
    bind_and_assume!(x);
    let _ = x;
    assert!(false);
}
