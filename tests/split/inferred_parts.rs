#[thrust_macros::requires(x >= 0)]
#[thrust_macros::ensures(result >= 1)]
fn bad(x: i64) -> i64 {
    x
}

fn double(x: i64) -> i64 {
    x + x
}

fn main() {
    bad(1);
    assert!(double(2) == 4);
}
