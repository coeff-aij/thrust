//@check-pass
//@compile-flags: -C debug-assertions=off
macro_rules! around {
    ($e:expr) => {{
        let x = 100i64;
        let _ = x;
        $e
    }};
}
fn main() {
    let x = 2i64;
    let v = around!(thrust_macros::block_contract_inline!(
        |x: i64| -> i64 requires(true), ensures(result == x), { x }
    ));
    assert!(v == 2);
}
