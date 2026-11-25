//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

fn main() {
    let n = rand();
    let z = n + 1;
    let mut x = n;
    let y = thrust_macros::block_contract_inline!(
        |mut x: i64| -> i64
        ensures(result == x && result >= 0),
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
