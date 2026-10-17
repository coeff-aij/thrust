#[thrust_macros::requires(amount <= balance)]
#[thrust_macros::ensures(result == balance - amount)]
fn withdraw(balance: i64, amount: i64) -> i64 {
    balance - amount
}

fn main() {
    withdraw(10, 30);
}
