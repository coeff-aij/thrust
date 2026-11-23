//@compile-flags: -C debug-assertions=off

// The analysis rejects code under a contract that a path enters without `block_requires!`.
// `block_contract!` cannot be entered so, being a braced block; this test writes the two marker
// forms it expands into by hand to keep that check covered: the `else` path of the `if` reaches
// `x += 1` without the marker, and the code after the contract would be read on the marker's
// path alone, where `c > 0` holds.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

fn main() {
    let c = rand();
    let mut x: i64 = 0;
    if c > 0 {
        thrust_macros::block_requires!(|x: i64| x == 0); //~ ERROR: the code under `block_requires!` is also reached by a path that does not pass it
    }
    x += 1;
    thrust_macros::block_ensures!(|x: i64| x == 1);
    assert!(c > 0);
}
