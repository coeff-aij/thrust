#[thrust::trusted]
#[thrust_macros::requires(x > 0)]
#[thrust_macros::ensures(result > x)]
fn bad(x: i64) -> i64 {
    x - 1
}

#[cfg(test)]
fn twin(x: i64) -> i64 {
    assert!(x == 0);
    x
}

#[cfg(not(test))]
fn twin(x: i64) -> i64 {
    x
}

fn main() {
    let a = bad(1);
    assert!(a > 1);
    let _ = twin(3);
}
