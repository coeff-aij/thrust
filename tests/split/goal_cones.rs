fn double(x: i64) -> i64 {
    x + x
}

fn main() {
    let a = double(2);
    assert!(a == 4);
    let b = double(3);
    assert!(b == 7);
}
