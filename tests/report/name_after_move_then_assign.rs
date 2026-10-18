fn take(v: Box<i64>) -> i64 { *v }
#[thrust::callable]
fn f(n: i64) -> i64 {
    let mut b = Box::new(0_i64);
    let c = b;
    let r = take(c);
    b = Box::new(7);
    assert!(*b == n + r);
    r
}
fn main() {}
