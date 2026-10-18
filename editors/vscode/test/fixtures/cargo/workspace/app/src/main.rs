#[thrust_macros::requires(x > 0)]
#[thrust_macros::ensures(result < x)]
fn dec(x: i64) -> i64 {
    x - 1
}

#[thrust_macros::requires(x > 0)]
#[thrust_macros::ensures(result > 0)]
fn shrink(x: i64) -> i64 {
    dec(x)
}

fn main() {
    assert!(shrink(2) == 1);
}
