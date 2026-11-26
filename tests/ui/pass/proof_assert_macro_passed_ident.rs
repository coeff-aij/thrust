//@check-pass
//@compile-flags: -C debug-assertions=off

// A macro binds `$x` from the caller's identifier and its annotation names `$x`: both have the
// caller's context, so the annotation names the variable the macro binds.
macro_rules! bind_and_check {
    ($x:ident) => {{
        let $x: i64 = 1;
        thrust_macros::proof_assert!(|$x: i64| $x == 1);
        let _ = $x;
    }};
}

fn main() {
    bind_and_check!(x);
}
