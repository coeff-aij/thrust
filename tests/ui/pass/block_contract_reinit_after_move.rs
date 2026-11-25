//@check-pass
//@compile-flags: -C debug-assertions=off

// A local moved out before the contract (`b`, `s`, the latter in the block that opens it) or
// under it (`c`) and set again by the code under the contract takes a fresh value after it, of
// which only what `block_ensures!` says holds.
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
    let d = Box::new(n);
    let mut s = (d, 1i64);
    let t = s;
    thrust_macros::block_requires!(|c: Box<i64>, n: i64| true);
    consume(c);
    b = Box::new(n + 1);
    c = Box::new(n + 2);
    s = (Box::new(n + 3), 2);
    thrust_macros::block_ensures!(|b: Box<i64>, c: Box<i64>, s: (Box<i64>, i64), n: i64|
        *b == n + 1 && *c == n + 2 && *s.0 == n + 3 && s.1 == 2);
    assert!(*b == n + 1 && *c == n + 2 && *s.0 == *t.0 + 3 && s.1 == t.1 + 1);
}
