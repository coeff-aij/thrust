#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == 2 * n)]
fn double_by_loop(n: i64) -> i64 {
    let mut i = 0;
    let mut s = 0;
    while i < n {
        i += 1;
        s += 2;
    }
    s
}

fn main() {
    assert!(double_by_loop(5) == 10);
}
