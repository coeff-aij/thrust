fn last_index(n: i64) -> i64 {
    let mut last = 0;
    for i in 0..n {
        assert!(i < n - 1);
        last = i;
    }
    last
}

fn main() {
    let _ = last_index(3);
}
