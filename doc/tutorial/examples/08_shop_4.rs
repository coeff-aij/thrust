#[thrust_macros::requires(amount <= balance)]
#[thrust_macros::ensures(result == balance - amount)]
fn withdraw(balance: i64, amount: i64) -> i64 {
    balance - amount
}

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == 3 * n)]
fn shipping(n: i64) -> i64 {
    let mut i = 0;
    let mut cost = 0;
    while i < n {
        cost += 3;
        i += 1;
    }
    cost
}

fn price(units: i64) -> i64 {
    if units >= 10 {
        units * 9
    } else {
        units * 10
    }
}

fn main() {
    let p = price(10);
    assert!(p == 90);
    let left = withdraw(200, p);
    assert!(left == 110);
    assert!(shipping(2) == 6);
}
