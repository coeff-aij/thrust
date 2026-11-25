//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `p` is written through, then re-pointed to `o` before an annotation that names `o`: the write
// stays with the referent `p` had.

#[thrust_macros::requires(*p == 0 && *o == 0)]
#[thrust_macros::ensures(!p == 5 && !o == 5)]
fn go<'a>(mut p: &'a mut i64, o: &'a mut i64) {
    *p = 5;
    p = o;
    thrust_macros::proof_assert!(|o: &mut i64| true);
    let _ = p;
}

fn main() {}
