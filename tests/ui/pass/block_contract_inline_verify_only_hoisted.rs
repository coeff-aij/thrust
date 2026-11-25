//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=host
#[thrust_macros::context]
#[thrust_macros::requires(x == 0)]
#[thrust_macros::ensures(result == 1)]
fn host(mut x: i64) -> i64 {
    thrust_macros::block_contract_inline!(
        |mut x: i64| -> () requires(true), ensures(x == old!(x) + 1), { x += 1; }
    );
    x
}
fn main() {}
