//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// As the pass twin, but the borrowed variable is asserted to hold 1, the value the call's
// reborrow gave the field, while `*s.r = 3` wrote it afterwards.
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
    *s.r = 3;
    assert!(s.k == 5);
    assert!(x == 1);
}
