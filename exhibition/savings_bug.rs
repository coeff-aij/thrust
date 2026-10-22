// Savings, with a bug: the monthly amount may be negative (a monthly charge).
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result >= start)]
fn save(start: i64, amount: i64, n: i64) -> i64 {
    let mut balance = start;
    let mut month = 0;
    while month < n {
        balance += amount;
        month += 1;
    }
    balance
}

fn main() {
    assert!(save(100, 10, 12) >= 100);
}
