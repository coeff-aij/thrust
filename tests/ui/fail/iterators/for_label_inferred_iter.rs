//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The outer `for` loop has no invariant, so Thrust infers it; the written invariant of the inner
// loop, its whole invariant, still carries the outer loop's iterator, which it names through the
// outer loop's label as `iter!('rows)`.
// Fail twin: at the inner head the outer range has stepped, so its `start` is not `0`.

use core::ops::Range;

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == 2 * n)]
fn f(n: i64) -> i64 {
    let mut c = 0;
    'rows: for _i in 0..n {
        for _j in 0..2i64 {
            thrust_macros::invariant!(|iter: Range<i64>, iter!('rows): Range<i64>, c: i64, n: thrust_models::FnParam<i64>|
                0 <= iter.start && iter.start <= 2 && iter.end == 2
                    && iter!('rows).start == 0 && iter!('rows).start <= iter!('rows).end && iter!('rows).end == n.at_entry()
                    && c == 2 * (iter!('rows).start - 1) + iter.start);
            c += 1;
        }
    }
    c
}

fn main() {
    assert!(f(3) == 6);
}
