//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A `&mut` in a struct field passed to a call in the code under the contract is reborrowed, so
// the call changes the struct and the contract does not keep the value it had before.
struct S<'a> {
    r: &'a mut i64,
    k: i64,
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!r == 1)]
fn set(r: &mut i64) {
    *r = 1;
}

fn main() {
    let mut x = 0_i64;
    let s = S { r: &mut x, k: 5 };
    thrust_macros::block_contract!(requires(|| true), ensures(|| true), {
        set(s.r);
    });
    let k = s.k;
    assert!(x == 0);
}
