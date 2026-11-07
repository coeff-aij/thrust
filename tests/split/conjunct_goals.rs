#[thrust_macros::requires(x > 0)]
#[thrust_macros::ensures(result > x)]
#[thrust_macros::ensures(result > 2)]
fn succ(x: i64) -> i64 {
    x + 1
}

fn main() {}
