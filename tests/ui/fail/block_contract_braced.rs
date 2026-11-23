//@error-in-other-file: Unsat

//@compile-flags: -C debug-assertions=off

// As the pass test, with an assertion the contract does not give.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

fn main() {
    let n = rand();
    let z = n + 1;
    let mut x = n;
    let y = thrust_macros::block_contract!(
        requires(|x: i64| true),
        ensures(|x: i64, result: i64| result == x && result >= 0),
        {
            x += 1;
            if x < 0 {
                x = -x;
            }
            x
        }
    );
    assert!(z == n + 1);
    assert!(y == x);
    assert!(y >= 1); // not in the contract
}
