//@check-pass
//@compile-flags: -C debug-assertions=off

// A macro binds `mut $x` from the caller's identifier, and the statement the caller passes names
// `x`: it is the variable the macro binds, though `mut` has the macro's context.
macro_rules! rebind {
    ($x:ident, $s:stmt) => {{
        let mut $x: i64 = 0;
        $x += 1;
        $s;
        let _ = $x;
    }};
}

fn main() {
    rebind!(x, thrust_macros::proof_assert!(|x: i64| x == 1));
}
