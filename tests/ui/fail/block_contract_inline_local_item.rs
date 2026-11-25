//@compile-flags: -C debug-assertions=off
// wrong twin: the host's local const K = 1 shadows the module's K = 2; the hoisted fn sees K = 2.
const K: i64 = 2;

#[thrust_macros::context]
#[thrust_macros::ensures(result == x + 2)]
fn host(x: i64) -> i64 {
    const K: i64 = 1; //~ ERROR: has an item statement
    thrust_macros::block_contract_inline!(
        |x: i64| -> i64 requires(true), ensures(result == x + 2), { x + K }
    )
}

fn main() {
    assert!(host(0) == 2);
}
