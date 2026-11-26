//@compile-flags: -C debug-assertions=off
// A block inside another is not supported.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}
fn main() {
    let x = rand();
    let y = thrust_macros::block_contract!( //~ ERROR: a block contract inside another block contract is not supported
        |x: i64| -> i64
        ensures(result == x + 2),
        {
            let z = thrust_macros::block_contract!(
                |x: i64| -> i64
                ensures(result == x + 1),
                { x + 1 }
            );
            z + 1
        }
    );
    assert!(y == x + 2);
}
