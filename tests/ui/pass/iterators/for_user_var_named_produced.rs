//@check-pass
//@compile-flags: -C debug-assertions=off -A unused
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// Under `#[context]`, a user's own variable named `produced` in a `for` loop's invariant that
// does not name `iter` is that variable: the loop is not desugared and the invariant reads it.

#[thrust_macros::context]
#[thrust::callable]
fn count(produced: i64, n: i64) -> i64 {
    let mut s = produced;
    for _i in 0..n {
        thrust_macros::invariant!(|produced: i64, s: i64| produced <= s);
        s += 1;
    }
    s - produced
}

fn main() {}
