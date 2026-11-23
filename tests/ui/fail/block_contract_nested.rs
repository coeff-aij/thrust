//@compile-flags: -C debug-assertions=off

// A contract inside another is not supported.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

fn main() {
    let x = rand();
    let y = thrust_macros::block_contract!( //~ ERROR: a block contract inside another block contract is not supported
        requires(|x: i64| x == x),
        ensures(|result: i64, x: i64| result == x + 2),
        {
            let z = thrust_macros::block_contract!(
                requires(|x: i64| x == x),
                ensures(|result: i64, x: i64| result == x + 1),
                { x + 1 }
            );
            z + 1
        }
    );
    assert!(y == x + 2);
}
