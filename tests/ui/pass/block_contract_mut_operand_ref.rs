//@check-pass
//@compile-flags: -C debug-assertions=off

// A `&mut` passed to a call in the code under the contract is reborrowed, so what the call
// ensures of the callee holds of the variable afterwards.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!r == 1)]
fn set(r: &mut i64) {
    *r = 1;
}

fn main() {
    let mut x = 0_i64;
    let b = &mut x;
    thrust_macros::block_contract!(requires(|| true), ensures(|b: &mut i64| !b == 1), {
        set(b);
    });
    assert!(x == 1);
}
