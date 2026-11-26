//@check-pass
//@compile-flags: -C debug-assertions=off
// The twin of `fail/block_contract_local_item_macro_fn.rs`: no macro declares a local `g`.
#[thrust_macros::ensures(result == a + 2)]
fn g(a: i64) -> i64 {
    a + 2
}

#[thrust_macros::context]
#[thrust_macros::ensures(result == x + 2)]
fn host(x: i64) -> i64 {
    thrust_macros::block_contract!(
        |x: i64| -> i64 requires(true), ensures(result == x + 2), { g(x) }
    )
}

fn main() {
    assert!(host(0) == 2);
}
