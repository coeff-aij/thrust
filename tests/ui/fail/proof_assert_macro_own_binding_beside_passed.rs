//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A name in a formula resolves with Rust's hygiene: in a `macro_rules!` macro that binds its own
// `x` beside a passed `$x`, the formula naming `x` refers to the macro's own binding, which is
// 0, so asserting 5 for it fails.
macro_rules! both {
    ($x:ident) => {{
        let x: i64 = 0;
        let $x: i64 = 5;
        thrust_macros::proof_assert!(|x: i64| x == 5);
        thrust_macros::proof_assert!(|$x: i64| $x == 5);
        let _ = (x, $x);
    }};
}

fn main() {
    both!(x);
}
