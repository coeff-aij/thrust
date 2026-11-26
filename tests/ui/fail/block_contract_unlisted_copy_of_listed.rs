//@compile-flags: -C debug-assertions=off
// `foo` is a copy of the listed `f`: after MIR copy propagation the body would seem to use `f`,
// while the hoisted function the block is verified as calls the module's `foo`.
fn foo(a: i64) -> i64 {
    a + 10
}

#[thrust_macros::context]
fn host<F: Fn(i64) -> i64 + Copy>(f: F) -> i64 {
    let foo = f;
    thrust_macros::block_contract!(
        |f: F| -> i64 requires(true), ensures(true), { foo(1) //~ ERROR: uses the variable `foo`
        }
    )
}

fn main() {}
