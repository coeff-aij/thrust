//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A local the code under the contract changes (`y`) has, after it, only what `ensures`
// says of it; one it leaves unchanged (`z`) keeps what held before. What held of `y` before the
// code (`y == m`) is not kept.
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
        requires(|x: i64| true),
        ensures(|x: i64, y: i64| y == x),
        {
            x += 1;
            y = x;
        }
    );
    assert!(z == n + 1);
    assert!(y == m);
}
