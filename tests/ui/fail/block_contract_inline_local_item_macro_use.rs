//@compile-flags: -C debug-assertions=off
// A macro declares a `use` in the host that makes `f` another function there than in the hoisted
// function.
mod other {
    pub fn f(a: i64) -> i64 {
        a + 1
    }
}
fn f(a: i64) -> i64 {
    a + 2
}
macro_rules! use_other {
    () => {
        use other::f; //~ ERROR: has an item statement
    };
}

#[thrust_macros::context]
fn host(x: i64) -> i64 {
    use_other!();
    thrust_macros::block_contract_inline!(
        |x: i64| -> i64 requires(true), ensures(result == x + 2), { f(x) }
    )
}

fn main() {
    let _ = host(0);
}
