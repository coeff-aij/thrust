//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
#[thrust_macros::context]
#[thrust_macros::requires(x == 0)]
#[thrust_macros::ensures(result == 1)]
fn bump<T: Copy>(mut x: i64, t: T) -> i64 {
    let mut y = t;
    thrust_macros::block_contract_fn!(
        |x: &mut i64, y: &mut T| -> ()
        requires(*x == 0),
        ensures(!x == 1),
        {
            *x += 1;
            let _ = y;
        }
    );
    x
}

fn main() {
    assert!(bump(0, 5i64) == 1);
}
