#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(2 * result == n * (n - 1))]
fn sum_below(n: i64) -> i64 {
    let mut i = 0;
    let mut s = 0;
    while i < n {
        s += i;
        i += 1;
    }
    s
}

fn main() {}
