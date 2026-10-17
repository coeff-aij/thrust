#[thrust_macros::requires(amount <= balance)]
#[thrust_macros::ensures(result == balance - amount)]
fn withdraw(balance: i64, amount: i64) -> i64 {
    balance - amount
}

fn pay(balance: i64, bill: i64) -> i64 {
    withdraw(balance, bill)
}

fn main() {
    let left = pay(80, 50);
    assert!(left == 30);
}
