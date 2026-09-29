//@check-pass
//@compile-flags: -C debug-assertions=off

const WORD_BITS: u64 = 64;

#[thrust_macros::requires(x <= u64::MAX / WORD_BITS)]
#[thrust_macros::ensures(result <= u64::MAX && result % WORD_BITS == 0)]
fn words_to_bits(x: u64) -> u64 {
    x * WORD_BITS
}

#[thrust_macros::requires(x == i64::MIN)]
#[thrust_macros::ensures(result == i64::MAX)]
fn flip(x: i64) -> i64 {
    -(x + 1)
}

#[thrust_macros::ensures(result == u128::MAX)]
fn top() -> u128 {
    u128::MAX
}

#[thrust_macros::ensures(result == i128::MIN)]
fn bottom() -> i128 {
    i128::MIN
}

fn main() {}
