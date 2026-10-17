fn count(n: i64) -> i64 {
    let mut c = 0;
    for i in 0..n {
        assert!(i < n);
        c += 1;
    }
    c
}

fn main() {
    let _ = count(3);
}
