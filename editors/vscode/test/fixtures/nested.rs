#[thrust::trusted]
#[thrust_macros::requires(x > 0)]
#[thrust_macros::ensures(result > x)]
fn outer(x: i64) -> i64 {
    fn inner(y: i64) -> i64 {
        y + 1
    }
    inner(x) - 2
}

fn main() {
    let a = outer(1);
    assert!(a > 1);
}
