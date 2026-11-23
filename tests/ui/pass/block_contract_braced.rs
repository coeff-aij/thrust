//@check-pass
//@compile-flags: -C debug-assertions=off

// `block_contract!` on a braced block: the block is checked from `requires` against `ensures`,
// and the code after it reads only the contract; `ensures` names the block's value `result`,
// and a local the block leaves unchanged (`z`) keeps what held before.
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
    assert!(y >= 0);
}
