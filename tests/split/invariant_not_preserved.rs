#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(2 * result == n * (n - 1))]
fn sum_below(n: i64) -> i64 {
    let mut i = 0;
    let mut s = 0;
    while i < n {
        thrust_macros::invariant!(|i: i64, s: i64, n: thrust_models::FnParam<i64>|
            0 <= i && i <= n.at_entry() && 2 * s == i * (i + 1));
        s += i;
        i += 1;
    }
    s
}

fn main() {}
