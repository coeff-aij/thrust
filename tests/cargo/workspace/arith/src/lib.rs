#[thrust_macros::requires(x >= 0)]
#[thrust_macros::ensures(result > x)]
pub fn inc(x: i64) -> i64 {
    x + 1
}
