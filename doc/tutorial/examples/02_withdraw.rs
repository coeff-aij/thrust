#[thrust_macros::requires(amount <= balance)]
#[thrust_macros::ensures(result == balance - amount)]
fn withdraw(balance: i64, amount: i64) -> i64 {
    balance - amount
}

#[thrust_macros::ensures(result >= 0)]
#[thrust_macros::ensures(result == x || result == -x)]
fn abs(x: i64) -> i64 {
    if x < 0 {
        -x
    } else {
        x
    }
}

fn main() {
    let b = withdraw(100, 30);
    assert!(b == 70);
    assert!(abs(-5) == 5);
}
