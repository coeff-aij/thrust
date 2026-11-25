//@check-pass
//@compile-flags: -C debug-assertions=off
// A variable the block changes (`y`) has, after it, only what `ensures` says of it; one it
// leaves unchanged (`z`) keeps what held before.
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
    thrust_macros::block_contract!(
        |mut x: i64, mut y: i64| -> ()
        ensures(y == x),
        {
            x += 1;
            y = x;
        }
    );
    assert!(z == n + 1);
    assert!(y == x);
}
