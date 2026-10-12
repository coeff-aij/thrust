#[thrust_macros::ensures(result == x + 1)]
pub fn inc(x: i64) -> i64 {
    x + 1
}
