//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The written invariant of an inner loop is its whole invariant, so it carries the outer `for`
// loop's iterator, which it names through the outer loop's label as `iter!('rows)`.

use core::ops::Range;

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == 2 * n)]
fn f(n: i64) -> i64 {
    let mut c = 0;
    'rows: for _i in 0..n {
        thrust_macros::invariant!(|iter: Range<i64>, c: i64, n: thrust_models::FnParam<i64>|
            0 <= iter.start && iter.start <= iter.end && iter.end == n.at_entry() && c == 2 * iter.start);
        for _j in 0..2i64 {
            thrust_macros::invariant!(|iter: Range<i64>, iter!('rows): Range<i64>, c: i64, n: thrust_models::FnParam<i64>|
                0 <= iter.start && iter.start <= 2 && iter.end == 2
                    && 1 <= iter!('rows).start && iter!('rows).start <= iter!('rows).end && iter!('rows).end == n.at_entry()
                    && c == 2 * (iter!('rows).start - 1) + iter.start);
            c += 1;
        }
    }
    c
}

fn main() {
    assert!(f(3) == 6);
}
