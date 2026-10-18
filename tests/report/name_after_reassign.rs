#[thrust::callable]
fn f(n: i64) -> i64 {
    let mut i = 0_i64;
    while i < n {
        thrust_macros::invariant!(|i: i64| i >= 0);
        i += 1;
    }
    let k = i;
    i = 5;
    assert!(k == n + 1);
    i
}

fn main() {}
