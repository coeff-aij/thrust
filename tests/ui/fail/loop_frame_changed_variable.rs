//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `k` is changed by the loop, so only the invariant says anything about it afterwards, while
// `n` keeps what held on entry.

#[thrust_macros::requires(n > 0)]
#[thrust_macros::ensures(true)]
fn f(n: i64) {
    let mut k = n;
    while k > 0 {
        thrust_macros::invariant!(|k: i64| k >= 0);
        k -= 1;
    }
    assert!(k == n);
}

fn main() {}
