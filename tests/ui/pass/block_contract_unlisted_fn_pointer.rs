//@check-pass
//@compile-flags: -C debug-assertions=off
// The twin of `fail/block_contract_unlisted_fn_pointer.rs`: the variable is not named `g`,
// so `g` is the module's function in place and in the extracted function.
fn g(a: i64) -> i64 {
    a * 100
}

#[thrust_macros::context]
#[thrust_macros::ensures(result == 100)]
fn host() -> i64 {
    let h = |a: i64| a + 1;
    let _ = h(0);
    thrust_macros::block_contract!(
        || -> i64 requires(true), ensures(result == 100), { g(1) }
    )
}

fn main() {
    assert!(host() == 100);
}
