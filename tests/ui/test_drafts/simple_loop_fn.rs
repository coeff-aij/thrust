fn incr(c: &mut i64, n: i64) {
    while *c < n {
        *c += 1;
    }
}

fn main() {
    let mut x = 5;
    let y = 10;
    incr(&mut x, y);
    assert!(x == y);
}
