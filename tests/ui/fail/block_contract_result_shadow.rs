//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

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
        requires(|x: i64| x == x),
        ensures(|result: i64| result == 5),
        { x + 1 }
    );
    assert!(y == x + 1);
    assert!(result == 5);
}
