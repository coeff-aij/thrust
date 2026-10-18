#[thrust_macros::requires(x >= 0)]
#[thrust_macros::ensures(result > x)]
fn next(x: i64) -> i64 {
    x
}

fn main() {
    next(0);
}
