//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The body of the block calls a function with a const generic parameter, which a contract names.
#[thrust_macros::requires(x == 0)]
#[thrust_macros::ensures(result == N)]
fn add_n<const N: usize>(x: usize) -> usize {
    x + N
}

fn main() {
    let mut x = 0usize;
    thrust_macros::block_contract!(
        |mut x: usize| -> ()
        requires(x == 0),
        ensures(x == 3),
        {
            x = add_n::<3>(x);
        }
    );
    assert!(x == 3);
}
