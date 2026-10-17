fn price(units: i64) -> i64 {
    units * 9
}

fn main() {
    assert!(price(10) == 91);
}
