fn double(x: i64) -> i64 {
    x + x
}

fn main() {
    let y = double(3);
    assert!(y == 6);
}
