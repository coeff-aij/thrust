//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `!p` is the final value of `p`. An `assume!` of it before the write that fixes it holds where
// the write keeps it; a `proof_assert!` of it there cannot be shown, since the write is later.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!p == 4)]
fn set(p: &mut i64) {
    *p = 3;
    thrust_macros::proof_assert!(|p: &mut i64| !p == 4);
    *p = 4;
}

fn main() {
    let mut a = 0;
    set(&mut a);
    assert!(a == 4);
}
