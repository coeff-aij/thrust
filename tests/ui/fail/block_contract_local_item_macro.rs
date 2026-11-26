// A macro declares the host's local `const K = 1`, which the hoisted function does not see.
const K: i64 = 2;
macro_rules! local_k {
    () => {
        const K: i64 = 1; //~ ERROR: has an item statement
    };
}

#[thrust_macros::context]
#[thrust_macros::ensures(result == x + 2)]
fn host(x: i64) -> i64 {
    local_k!();
    thrust_macros::block_contract!(
        |x: i64| -> i64 requires(true), ensures(result == x + 2), { x + K }
    )
}

fn main() {
    assert!(host(0) == 2);
}
