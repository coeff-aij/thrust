//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
#[thrust_macros::context]
#[thrust_macros::requires(x == 0 && N == 3)]
#[thrust_macros::ensures(result == 3)]
fn add_n<const N: usize>(mut x: i64) -> i64 {
    thrust_macros::block_contract!(
        |mut x: i64| -> ()
        requires(x == 0),
        ensures(x == N as i64),
        {
            x += N as i64;
        }
    );
    x
}

fn main() {
    assert!(add_n::<3>(0) == 3);
}
