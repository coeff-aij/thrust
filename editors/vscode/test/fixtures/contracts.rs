#[thrust_macros::requires(x >= 0)]
#[thrust_macros::ensures(result >= x)]
fn grow(x: i64) -> i64 {
    x + 1
}

fn main() {
    let y = grow(1);
    assert!(y == 2);
}
