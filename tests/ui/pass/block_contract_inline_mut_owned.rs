//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `mut` owned variable of the block: `ensures` names its final value as `x` and its entry
// value as `old!(x)`.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

fn main() {
    let n = rand();
    let mut x = 5;
    let y = thrust_macros::block_contract_inline!(
        |mut x: i64| -> i64
        requires(x == 5),
        ensures(old!(x) == 5 && x == 6 && result == 7),
        {
            x += 1;
            x + 1
        }
    );
    assert!(x == 6);
    assert!(y == 7);
    let _ = n;
}
