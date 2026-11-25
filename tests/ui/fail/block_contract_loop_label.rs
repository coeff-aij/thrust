//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// As the pass test, with an `ensures` one more than the code gives.
use thrust_models::FnParam;
use core::ops::Range;

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == n)]
fn f(n: i64) -> i64 {
    let mut c = 0;
    'rows: for _i in 0..n {
        thrust_macros::invariant!(|iter: Range<i64>, c: i64, n: FnParam<i64>|
            0 <= iter.start && iter.start <= iter.end && iter.end == n.at_entry() && c == iter.start);
        c = thrust_macros::block_contract!(
            requires(|c: i64, iter!('rows): Range<i64>| c + 1 == iter!('rows).start),
            ensures(|result: i64, iter!('rows): Range<i64>| result == iter!('rows).start + 1),
            { c + 1 }
        );
    }
    c
}

fn main() {
    assert!(f(3) == 3);
}
