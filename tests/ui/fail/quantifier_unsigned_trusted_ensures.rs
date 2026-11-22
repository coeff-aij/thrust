//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

// A variable a trusted `ensures` binds at an unsigned type ranges over the values of the type: the
// postcondition says the result is the least `u64`, which is `0`.
use thrust_models::forall;

#[thrust::trusted]
#[thrust_macros::ensures(forall(|n: u64| result <= n))]
fn least() -> u64 {
    0
}

fn main() {
    let r = least();
    assert!(r == 1);
}
