fn mul(x: i64, y: i64) -> i64 {
    let mut r = 0;
    let mut i = 0;
    while i < y {
        r += x;
        i += 1;
    }
    r
}

fn main() {
    let a = mul(7, 9);
    let b = mul(9, 7);
    assert!(a * b == 3969);
}
