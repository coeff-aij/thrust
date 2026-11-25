//@compile-flags: -C debug-assertions=off
// In a closure, a captured variable the body uses and the block does not list: the extracted
// function does not see it, and `foo` there is the module's function.
fn foo(a: i64) -> i64 {
    a + 10
}

#[thrust_macros::context]
fn host<F: Fn(i64) -> i64 + Copy>(f: F) -> i64 {
    let foo = f;
    let c = move |k: i64| {
        thrust_macros::block_contract_inline!(
            |k: i64| -> i64 requires(true), ensures(true), { foo(k) //~ ERROR: uses the variable `foo`
            }
        )
    };
    c(1)
}

fn main() {}
