//@check-pass
//@compile-flags: -C debug-assertions=off

// An intermediate fact in a loop body, checked there and assumed for the rest of the body.
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == 2 * n)]
fn double(n: i64) -> i64 {
    let mut i = 0;
    let mut s = 0;
    while i < n {
        thrust_macros::invariant!(|i: i64, s: i64, n: i64| s == 2 * i && i <= n);
        s += 1;
        thrust_macros::proof_assert!(|i: i64, s: i64| s == 2 * i + 1);
        s += 1;
        i += 1;
    }
    s
}

fn main() {
    assert!(double(3) == 6);
}
