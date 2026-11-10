//@check-pass
//@compile-flags: -C debug-assertions=off

// An invariant names the binding in scope at the loop: the inner `x`, not the outer one it
// shadows, though both are live at the loop head.

use thrust_models::FnParam;

#[thrust::callable]
fn f(x0: i64) -> i64 {
    let x = x0;
    let r = {
        let x = x0 + 1;
        let mut i: i64 = 0;
        while i < 3 {
            thrust_macros::invariant!(|x: i64, x0: FnParam<i64>, i: i64| x == x0.at_entry() + 1 && i >= 0);
            i += 1;
        }
        x
    };
    x + r
}

fn main() {}
