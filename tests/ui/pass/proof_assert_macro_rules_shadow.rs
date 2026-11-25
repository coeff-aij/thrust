//@check-pass
//@compile-flags: -C debug-assertions=off

// A name in a formula resolves with Rust's hygiene: the `x` a `macro_rules!` macro binds is not
// the caller's `x`, which the statement passed to the macro names.
macro_rules! with_zero {
    ($s:stmt) => {{
        let x: i64 = 0;
        $s;
        let _ = x;
    }};
}

fn main() {
    let x: i64 = 5;
    with_zero!(thrust_macros::proof_assert!(|x: i64| x == 5));
    assert!(x == 5);
}
