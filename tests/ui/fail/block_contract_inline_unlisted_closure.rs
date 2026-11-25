//@compile-flags: -C debug-assertions=off
// A closure the body calls shadows a function of the module in place only: the hoisted function
// the block is verified as does not see the closure and calls the module's `foo`.
fn foo(a: i64) -> i64 {
    a + 10
}

#[thrust_macros::context]
#[thrust_macros::ensures(result == 11)]
fn host() -> i64 {
    let foo = |a: i64| a + 1;
    thrust_macros::block_contract_inline!(
        || -> i64 requires(true), ensures(result == 11), { foo(1) //~ ERROR: uses the variable `foo`
        }
    )
}

fn main() {
    assert!(host() == 11);
}
