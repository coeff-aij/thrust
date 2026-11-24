//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A `&mut` in a tuple field passed to a call in the code under the contract is reborrowed, so
// the call changes the tuple and the contract does not keep the value it had before.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!r == 1)]
fn set(r: &mut i64) {
    *r = 1;
}

fn main() {
    let mut x = 0_i64;
    let s = (&mut x, 5_i64);
    thrust_macros::block_contract!(requires(|| true), ensures(|| true), {
        set(s.0);
    });
    let k = s.1;
    assert!(x == 0);
}
