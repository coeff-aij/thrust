//@check-pass
//@compile-flags: -C debug-assertions=off

// A local the code under the contract changes (`y`) has, after it, only what `block_ensures!`
// says of it; one it leaves unchanged (`z`) keeps what held before.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

fn main() {
    let n = rand();
    let m = rand();
    let z = n + 1;
    let mut x = n;
    let mut y = m;
    thrust_macros::block_requires!(|x: i64| true);
    x += 1;
    y = x;
    thrust_macros::block_ensures!(|x: i64, y: i64| y == x);
    assert!(z == n + 1);
    assert!(y == x);
}
