//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `for` whose body starts with two invariants naming the iterator: each of them names the
// desugared loop's `iter`.

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == n)]
fn count(n: i64) -> i64 {
    let mut c = 0;
    for _i in 0..n {
        thrust_macros::invariant!(|iter: core::ops::Range<i64>, c: i64, n: thrust_models::FnParam<i64>|
            0 <= c && c <= n.at_entry() && iter.end == n.at_entry());
        thrust_macros::invariant!(|iter: core::ops::Range<i64>, c: i64| iter.start == c);
        c += 1;
    }
    c
}

fn main() {
    assert!(count(3) == 4);
}
