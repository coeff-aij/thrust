#[thrust_macros::requires(x > 0)]
#[thrust_macros::requires(x < 100)]
#[thrust_macros::ensures(true)]
fn g(x: i64) -> i64 {
    x
}

fn h<T>(_t: T, x: i64) -> i64 {
    g(x)
}

#[thrust::split_goals]
fn m() {
    let _ = h(1i64, 5);
}

fn main() {
    m();
}
