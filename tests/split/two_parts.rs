#[thrust_macros::requires(x >= 0)]
#[thrust_macros::ensures(result >= 1)]
fn good(x: i64) -> i64 {
    x + 1
}

#[thrust_macros::requires(x >= 0)]
#[thrust_macros::ensures(result >= 1)]
fn bad(x: i64) -> i64 {
    x
}

fn main() {
    good(1);
    bad(1);
}
