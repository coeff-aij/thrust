//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// As the pass twin, but the borrowed variable is asserted to hold 1, the value the call's
// reborrow gave the field, while `*s.0 = 3` wrote it afterwards.
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
    *s.0 = 3;
    assert!(s.1 == 5);
    assert!(x == 1);
}
