//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// wrong twin: a macro binds its own hygienic `x = 100` around the block; the block's `x` is the user's 2.
macro_rules! around {
    ($e:expr) => {{
        let x = 100i64;
        let _ = x;
        $e
    }};
}
fn main() {
    let x = 2i64;
    let v = around!(thrust_macros::block_contract!(
        |x: i64| -> i64 requires(true), ensures(result == x), { x }
    ));
    assert!(v == 100);
}
