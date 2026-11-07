fn add_one(x: i64) -> i64 {
    x + 1
}

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == n)]
fn count_to(n: i64) -> i64 {
    let mut i = 0;
    while i < n {
        i += 1;
    }
    i
}

fn main() {
    let a = add_one(1);
    assert!(a == 2);
    let c = count_to(5);
    assert!(c == 5);
}
