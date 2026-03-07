//@check-pass

#[thrust::requires(f.precondition(x))]
#[thrust::ensures(f.postcondition(x, result))]
fn apply<F: Fn(i64) -> i64>(f: F, x: i64) -> i64 {
    // f(x) // correct
    x // incorrect
}

#[thrust::ensures(result == x)]
fn id(x: i64) -> i64 {
    x
}

#[thrust::ensures(result == 2 * x)]
fn double(x: i64) -> i64 {
    x + x
}

fn main() {
    let x = 1;

    assert!(apply(id, x) == x);
    assert!(apply(double, x) != x);
}
