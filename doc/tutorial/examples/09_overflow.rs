#[thrust::callable]
fn next(x: i64) -> i64 {
    let y = x + 1;
    assert!(y > x);
    y
}

fn main() {}
