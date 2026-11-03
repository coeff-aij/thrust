//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_FOR_LOOP_HISTORY=1 THRUST_SOLVER_TIMEOUT_SECS=120

// With `THRUST_FOR_LOOP_HISTORY=1`, the history of the outer `for` loop, which has no invariant,
// is conjoined at the heads of the loops inside it: the annotated one, whose written invariant
// cannot name the outer ghosts, and the one left to inference.

use core::ops::Range;

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result > 0)]
fn f(n: i64) -> i64 {
    let mut c = 0;
    for _i in 0..n {
        for _j in 0..2i64 {
            thrust_macros::invariant!(|iter: Range<i64>, c: i64| c >= 0);
            c += 1;
        }
        for _k in 0..2i64 {
            c += 1;
        }
    }
    c
}

fn main() {
    f(3);
}
