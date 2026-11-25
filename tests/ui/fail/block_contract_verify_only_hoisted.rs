//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=host
// wrong twin: the body breaks the block's ensures; only `host` is selected, its block is hoisted.
#[thrust_macros::context]
#[thrust_macros::requires(x == 0)]
#[thrust_macros::ensures(result == 1)]
fn host(mut x: i64) -> i64 {
    thrust_macros::block_contract!(
        |mut x: i64| -> () requires(true), ensures(x == old!(x) + 1), { x += 2; }
    );
    x
}
fn main() {}
