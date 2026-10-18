#[thrust_macros::predicate]
fn positive(x: i64) -> bool {
    x > 0
}

#[thrust::ignored]
fn log(x: i64) -> i64 {
    x
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x + 1)]
fn inc(x: i64) -> i64 {
    log(x) + 1
}

#[thrust_macros::requires(positive(x))]
#[thrust_macros::ensures(result > x)]
fn double(x: i64) -> i64 {
    x + x
}

fn twice(x: i64) -> i64 {
    let add = |y: i64| y + x;
    add(x)
}

fn main() {
    assert!(inc(1) == 2);
    assert!(double(1) > 1);
    assert!(twice(2) == 4);
}
