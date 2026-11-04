//@check-pass
//@compile-flags: -C debug-assertions=off

// A `closure!` contract over a parameter pattern that destructures a reference, as in
// `|&(_, x)| ..`: its clauses read the bound name as the referent's field.
fn main() {
    let p = (-1i64, 4i64);
    let f = thrust_macros::closure!(
        requires(x > 0),
        ensures(result == x + 1),
        |&(_, x): &(i64, i64)| -> i64 { x + 1 },
    );
    let r = f(&p);
    assert!(r == 5);
}
