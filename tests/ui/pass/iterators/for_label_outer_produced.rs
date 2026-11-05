//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An inner loop's invariant names the outer `for` loop's `produced`, `iter_old` and `iter` through
// the outer loop's label. Being the inner loop's whole invariant, it restates
// `produces(iter_old, produced, iter)` of the outer ghosts, which the outer loop's invariant
// conjoins and so needs again after the inner loop.

use core::ops::Range;
use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result >= 0)]
fn f(n: i64) -> i64 {
    let mut c = 0;
    'rows: for _i in 0..n {
        thrust_macros::invariant!(|iter: Range<i64>, produced: Ghost<Seq<Int>>, c: i64|
            c == 2 * produced.len());
        for _j in 0..2i64 {
            thrust_macros::invariant!(|iter: Range<i64>, iter!('rows): Range<i64>, iter_old!('rows): Ghost<Range<i64>>, produced!('rows): Ghost<Seq<Int>>, c: i64|
                0 <= iter.start && iter.start <= 2 && iter.end == 2
                    && <Range<i64> as IteratorSpec>::produces(iter_old!('rows), produced!('rows), iter!('rows))
                    && 1 <= produced!('rows).len()
                    && c == 2 * (produced!('rows).len() - 1) + iter.start);
            c += 1;
        }
    }
    c
}

fn main() {
    assert!(f(3) >= 0);
}
