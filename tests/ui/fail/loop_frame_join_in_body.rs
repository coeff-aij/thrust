//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `n` is used after a join inside the loop body, whose precondition Thrust infers.

#[thrust_macros::requires(n > 0)]
#[thrust_macros::ensures(true)]
fn f(n: i64, c: bool) {
    let mut i = 0_i64;
    while i < 10 {
        thrust_macros::invariant!(|i: i64| i >= 0);
        if c {
            i += 1;
        } else {
            i += 2;
        }
        assert!(n > 1);
    }
}

fn main() {}
