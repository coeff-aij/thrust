//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The code between `block_requires!` and `block_ensures!` is checked against the contract, and
// the code after it reads the contract and the locals the code leaves unchanged.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

fn main() {
    let n = rand();
    let mut x = 0i64;
    thrust_macros::block_requires!(|x: i64| x == 0);
    x += 1;
    thrust_macros::block_ensures!(|x: i64| x == 2);
    assert!(x == 2);
    assert!(n == n);
}
