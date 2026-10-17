#[thrust_macros::requires(a <= b)]
#[thrust_macros::ensures(result == b - a)]
fn withdraw(b: i64, a: i64) -> i64 {
    b - a - 1
}

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == n)]
fn count_to(n: i64) -> i64 {
    let mut i = 0;
    let mut s = 0;
    while i < n {
        i += 1;
        s += 2;
    }
    s
}

fn main() {
    let r = withdraw(10, 3);
    assert!(r == 7);
    let c = count_to(3);
    assert!(c == 3);
}
