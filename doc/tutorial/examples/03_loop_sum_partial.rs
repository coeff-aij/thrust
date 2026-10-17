#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(2 * result == n * (n - 1))]
fn sum_below(n: i64) -> i64 {
    let mut i = 0;
    let mut s = 0;
    while i < n {
        thrust_macros::partial_invariant!(|i: i64, s: i64| 2 * s == i * (i - 1));
        s += i;
        i += 1;
    }
    s
}

fn main() {}
