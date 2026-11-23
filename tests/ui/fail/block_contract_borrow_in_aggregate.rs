//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A borrow moved into an aggregate before the contract is resolved where the aggregate ends,
// after the code under the contract, not by passing over the code.
fn main() {
    let mut a = 1i64;
    let mut y = 0i64;
    let p = (&mut a, 0i64);
    thrust_macros::block_contract!(
        requires(|y: i64| y == 0),
        ensures(|y: i64| y == 1),
        {
            y += 1;
        }
    );
    *p.0 = 2;
    assert!(y == 1 && a == 1);
}
