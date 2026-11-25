//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use std::ops::ControlFlow;

fn main() {
    let mut x = 0i64;
    let mut n = 0i64;
    loop {
        let flow = thrust_macros::block_contract_fn!(
            |x: &mut i64| -> ControlFlow<i64, ()>
            requires(*x >= 0 && *x <= 3),
            ensures(match result { ControlFlow::Break(v) => v == !x && !x == 4, ControlFlow::Continue(()) => !x == *x + 1 && !x <= 3 }),
            {
                *x += 1;
                if *x > 3 {
                    return ControlFlow::Break(*x);
                }
                ControlFlow::Continue(())
            }
        );
        match flow {
            ControlFlow::Break(v) => {
                n = v;
                break;
            }
            ControlFlow::Continue(()) => {}
        }
    }
    assert!(n == 4);
}
