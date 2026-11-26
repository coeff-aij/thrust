//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// `ensures`' `result` names the block's value, also where a variable outside the block is named
// `result`, which keeps its value after the block.
// As the pass test, with an `ensures` that reads the local named `result` (5) as the block's value.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}
fn main() {
    let result: i64 = 5;
    let x = rand();
    let y = thrust_macros::block_contract!(
        |x: i64| -> i64
        ensures(result == 5),
        { x + 1 }
    );
    assert!(y == x + 1);
    assert!(result == 5);
}
