//@compile-flags: -C debug-assertions=off
// A macro declares a local `fn g` in the host that shadows the module's `g` there only.
fn g(a: i64) -> i64 {
    a + 2
}
macro_rules! local_g {
    () => {
        fn g(a: i64) -> i64 { //~ ERROR: has an item statement
            a + 1
        }
    };
}

#[thrust_macros::context]
fn host(x: i64) -> i64 {
    local_g!();
    thrust_macros::block_contract!(
        |x: i64| -> i64 requires(true), ensures(result == x + 2), { g(x) }
    )
}

fn main() {
    let _ = host(0);
}
