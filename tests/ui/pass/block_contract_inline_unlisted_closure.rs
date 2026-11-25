//@check-pass
//@compile-flags: -C debug-assertions=off
// The twin of `fail/block_contract_inline_unlisted_closure.rs`: no variable shadows the module's
// `foo`, and a variable the body uses is a parameter.
fn foo(a: i64) -> i64 {
    a + 10
}

#[thrust_macros::context]
#[thrust_macros::ensures(result == 11)]
fn host() -> i64 {
    let k = 1i64;
    thrust_macros::block_contract_inline!(
        |k: i64| -> i64 requires(true), ensures(result == 10 + k), { foo(k) }
    )
}

fn main() {
    assert!(host() == 11);
}
