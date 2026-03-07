//@check-pass

#[thrust::ensures(result == 2 * x)]
fn double(x: i64) -> i64 {
    x + x
}

fn triple(x: i64) -> i64 {
    x + double(x)
}

fn main() {
    let x = 5;
    assert!(x * 3 == triple(x));
}
