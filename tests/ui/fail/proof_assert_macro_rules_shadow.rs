//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A name in a formula resolves with Rust's hygiene: the `x` a `macro_rules!` macro binds is not
// the caller's `x`, so the `assume!` is of the caller's `x`, which is 5, not 0.
macro_rules! with_zero {
    ($s:stmt) => {{
        let x: i64 = 0;
        $s;
        let _ = x;
    }};
}

fn main() {
    let x: i64 = 5;
    with_zero!(thrust_macros::assume!(|x: i64| x == 5));
    assert!(x == 0);
}
