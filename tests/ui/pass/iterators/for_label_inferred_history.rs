//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_FOR_LOOP_HISTORY=1 THRUST_SOLVER_TIMEOUT_SECS=120

// With `THRUST_FOR_LOOP_HISTORY=1`, the outer `for` loop, which has no invariant and whose
// iterator the first inner loop's invariant names as `iter!('rows)`, keeps no history, while the
// second inner loop, with no invariant, gets one; the two loops' ghosts do not collide.

use core::ops::Range;

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result >= 0)]
fn f(n: i64) -> i64 {
    let mut c = 0;
    'rows: for _i in 0..n {
        for _j in 0..2i64 {
            thrust_macros::invariant!(|iter: Range<i64>, iter!('rows): Range<i64>, c: i64|
                c >= 0 && 1 <= iter!('rows).start);
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
