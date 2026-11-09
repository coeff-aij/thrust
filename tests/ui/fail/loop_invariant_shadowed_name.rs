//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The twin of `pass/loop_invariant_shadowed_name.rs`: the invariant states the outer `x`'s value
// of the inner `x`, which it reads, so it does not hold.

use thrust_models::FnParam;

#[thrust::callable]
fn f(x0: i64) -> i64 {
    let x = x0;
    let r = {
        let x = x0 + 1;
        let mut i: i64 = 0;
        while i < 3 {
            thrust_macros::invariant!(|x: i64, x0: FnParam<i64>, i: i64| x == x0.at_entry() && i >= 0);
            i += 1;
        }
        x
    };
    x + r
}

fn main() {}
