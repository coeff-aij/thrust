//@check-pass
//@compile-flags: -C debug-assertions=off

// `ensures`' `result` names the block's value, also where a local of the body is named `result`,
// which keeps its value after the block.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

fn main() {
    let result: i64 = 5;
    let x = rand();
    let y = thrust_macros::block_contract!(
        requires(|x: i64| x == x),
        ensures(|result: i64, x: i64| result == x + 1),
        { x + 1 }
    );
    assert!(y == x + 1);
    assert!(result == 5);
}
