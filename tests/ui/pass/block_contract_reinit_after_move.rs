//@check-pass
//@compile-flags: -C debug-assertions=off

// A local moved out before the contract (`b`) or under it (`c`) and set again by the code under
// the contract takes a fresh value after it, of which only what `block_ensures!` says holds.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

#[thrust::trusted]
#[thrust::callable]
fn consume(_b: Box<i64>) {}

fn main() {
    let mut b = Box::new(rand());
    let mut c = Box::new(rand());
    consume(b);
    let n = rand();
    thrust_macros::block_requires!(|c: Box<i64>, n: i64| true);
    consume(c);
    b = Box::new(n + 1);
    c = Box::new(n + 2);
    thrust_macros::block_ensures!(|b: Box<i64>, c: Box<i64>, n: i64| *b == n + 1 && *c == n + 2);
    assert!(*b == n + 1 && *c == n + 2);
}
