//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `block_contract!` in the body of a labelled `for` loop names the loop's iterator through the
// label, `iter!('rows)`, in its formulas, as the marker forms it expands into do.

use core::ops::Range;

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == n)]
fn f(n: i64) -> i64 {
    let mut c = 0;
    'rows: for _i in 0..n {
        thrust_macros::invariant!(|iter: Range<i64>, c: i64, n: thrust_models::FnParam<i64>|
            0 <= iter.start && iter.start <= iter.end && iter.end == n.at_entry() && c == iter.start);
        c = thrust_macros::block_contract!(
            requires(|c: i64, iter!('rows): Range<i64>| c + 1 == iter!('rows).start),
            ensures(|result: i64, iter!('rows): Range<i64>| result == iter!('rows).start),
            { c + 1 }
        );
    }
    c
}

fn main() {
    assert!(f(3) == 3);
}
