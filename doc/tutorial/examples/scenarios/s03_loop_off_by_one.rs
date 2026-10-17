#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == 3 * n)]
fn shipping(n: i64) -> i64 {
    let mut i = 0;
    let mut cost = 0;
    while i <= n {
        cost += 3;
        i += 1;
    }
    cost
}

fn main() {
    assert!(shipping(2) == 6);
}
