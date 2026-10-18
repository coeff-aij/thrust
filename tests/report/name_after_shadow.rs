#[thrust::callable]
fn f(n: i64) -> i64 {
    let mut i = 0_i64;
    while i < n {
        thrust_macros::invariant!(|i: i64| i >= 0);
        i += 1;
    }
    let i = 3_i64;
    let j = i + 1;
    assert!(j == n);
    j
}

fn main() {}
