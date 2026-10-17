fn count_to(n: i64) -> i64 {
    let mut i = 0_i64;
    while i < n {
        thrust_macros::invariant!(|i: i64| i >= 1);
        i += 1;
    }
    i
}

fn main() {
    assert!(count_to(3) >= 0);
}
