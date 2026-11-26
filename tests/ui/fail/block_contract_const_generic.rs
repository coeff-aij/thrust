//@error-in-other-file: `block_contract!` in `add_n` is not supported yet
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A function with a const generic parameter does not take a block contract yet; the error says so.
#[thrust_macros::context]
#[thrust_macros::requires(x == 0 && N == 3)]
#[thrust_macros::ensures(result == 3)]
fn add_n<const N: usize>(mut x: usize) -> usize {
    thrust_macros::block_contract!(
        |mut x: usize| -> ()
        requires(x == 0),
        ensures(x == N),
        {
            x += N;
        }
    );
    x
}

fn main() {
    assert!(add_n::<3>(0) == 3);
}
