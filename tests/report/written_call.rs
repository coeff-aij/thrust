#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result >= 0)]
#[thrust::trusted]
fn natural() -> i64 {
    unimplemented!()
}

fn main() {
    let n = natural();
    assert!(n > 0);
}
