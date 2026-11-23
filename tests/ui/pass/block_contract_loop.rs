//@check-pass
//@compile-flags: -C debug-assertions=off

// The code under a contract may start with a loop, whose invariant is inferred over the
// variables the code uses; `k`, which it does not use, keeps its value after it.
fn main() {
    let mut i = 0i64;
    let k = 7i64;
    thrust_macros::block_contract!(
        requires(|i: i64| i == 0),
        ensures(|i: i64| i == 10),
        {
            while i < 10 {
                i += 1;
            }
        }
    );
    assert!(i == 10 && k == 7);
}
