//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=conversions

// The code under the contract has the facts of the types of the variables it takes, which
// `block_requires!` does not restate: `n >= 0` of the `u32` and the range of the `u8` that `o`
// holds, and nothing stronger: `n` may be 0.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> u32 {
    unimplemented!()
}

#[thrust::trusted]
#[thrust::callable]
fn rand_byte() -> Option<u8> {
    unimplemented!()
}

#[thrust::trusted]
#[thrust::callable]
fn coin() -> bool {
    unimplemented!()
}

fn main() {
    let n = rand();
    let o = rand_byte();
    let c = coin();
    thrust_macros::block_requires!(|n: u32, o: Option<u8>, c: bool| true);
    let m = n as i64;
    let p: i64 = match o {
        Some(x) => x as i64,
        None => 0,
    };
    let k: i64 = if c { 1 } else { 2 };
    thrust_macros::block_ensures!(|m: i64, p: i64, k: i64| m + k >= 2 && p + k < 258);
    assert!(m + k >= 2 && p + k < 258);
}
