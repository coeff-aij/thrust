#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == n)]
fn count(n: i64) -> i64 {
    let mut i = 0;
    while i < n {
        i += 1;
    }
    i
}

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result >= 0)]
fn sum(n: i64) -> i64 {
    let mut s = 0;
    let mut i = 0;
    while i < n {
        s += i;
        i += 1;
    }
    s
}

fn main() {
    let a = count(3);
    let b = sum(4);
    assert!(a + b >= 3);
}
