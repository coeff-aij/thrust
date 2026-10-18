fn take(v: Box<i64>) -> i64 { *v }

#[thrust::callable]
fn f(n: i64) -> i64 {
    let mut b = Box::new(0_i64);
    while *b < n {
        thrust_macros::invariant!(|b: Box<i64>| *b >= 0);
        *b += 1;
    }
    let c = b;
    let r = take(c);
    assert!(r == n + 1);
    r
}

fn main() {}
