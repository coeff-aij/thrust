fn price(units: i64) -> i64 {
    if units >= 10 {
        units * 9
    } else {
        units * 10
    }
}

fn main() {
    let p = price(10);
    assert!(p == 90);
}
