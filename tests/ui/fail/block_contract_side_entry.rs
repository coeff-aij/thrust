//@compile-flags: -C debug-assertions=off

// The code under a contract is entered only through `block_requires!`: here the `else` path of
// the `if` reaches `x += 1` without the marker, and the analysis would read the code after the
// contract on the marker's path alone, where `c > 0` holds.
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
