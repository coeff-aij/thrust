//@check-pass
//@compile-flags: -C debug-assertions=off

// The code under the contract starts from `block_requires!` alone, which is checked where it is
// written.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

fn main() {
    let n = rand();
    let mut x = if n > 0 { n } else { 1 };
    thrust_macros::block_requires!(|x: i64| x > 0);
    x = x * 2;
    thrust_macros::block_ensures!(|x: i64| x > 1);
    assert!(x > 1);
}
