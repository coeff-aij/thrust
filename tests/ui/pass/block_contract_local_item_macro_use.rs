//@check-pass
//@compile-flags: -C debug-assertions=off
// The twin of `fail/block_contract_local_item_macro_use.rs`: no macro declares the `use`.
mod other {
    pub fn f(a: i64) -> i64 {
        a + 1
    }
}
#[thrust_macros::ensures(result == a + 2)]
fn f(a: i64) -> i64 {
    a + 2
}

#[thrust_macros::context]
#[thrust_macros::ensures(result == x + 2)]
fn host(x: i64) -> i64 {
    thrust_macros::block_contract!(
        |x: i64| -> i64 requires(true), ensures(result == x + 2), { f(x) }
    )
}

fn main() {
    assert!(host(0) == 2);
    let _ = other::f(0);
}
