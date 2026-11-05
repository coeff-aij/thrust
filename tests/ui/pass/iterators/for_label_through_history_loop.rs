//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_FOR_LOOP_HISTORY=1 THRUST_SOLVER_TIMEOUT_SECS=120

// With `THRUST_FOR_LOOP_HISTORY=1`, a loop with no invariant between the outer loop `'rows` and
// the annotated loop that names `iter!('rows)` gets the history, whose ghosts have fixed names;
// the reference still names the outer loop's iterator, not the middle loop's of the same type.

use core::ops::Range;

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result >= 0)]
fn f(n: i64) -> i64 {
    let mut c = 0;
    'rows: for _i in 0..n {
        for _m in 0..1i64 {
            for _j in 0..2i64 {
                thrust_macros::invariant!(|iter: Range<i64>, iter!('rows): Range<i64>, c: i64, n: thrust_models::FnParam<i64>|
                    c >= 0 && 1 <= iter!('rows).start && iter!('rows).end == n.at_entry());
                c += 1;
            }
        }
    }
    c
}

fn main() {
    f(3);
}
