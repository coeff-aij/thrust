//@compile-flags: -C debug-assertions=off
// A function-pointer variable the body calls shadows a function of the module in place only.
fn g(a: i64) -> i64 {
    a * 100
}

#[thrust_macros::context]
#[thrust_macros::ensures(result == 100)]
fn host() -> i64 {
    let g: fn(i64) -> i64 = |a| a + 1;
    thrust_macros::block_contract!(
        || -> i64 requires(true), ensures(result == 100), { g(1) //~ ERROR: uses the variable `g`
        }
    )
}

fn main() {
    assert!(host() == 100);
}
