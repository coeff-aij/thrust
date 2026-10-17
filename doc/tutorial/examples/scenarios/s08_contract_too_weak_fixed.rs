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
    assert!(abs(-5) == 5);
}
