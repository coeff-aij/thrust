//@check-pass
//@compile-flags: -C debug-assertions=off

// `closure!` contracts over parameter patterns that destructure a reference: written out, as in
// `|&(_, x)| ..`, where the clauses read `x` as the referent's field, and left to match
// ergonomics, as in `|(_, y)| ..`, where `y` is a reference to it.
fn main() {
    let p = (-1i64, 4i64);
    let f = thrust_macros::closure!(
        requires(x > 0),
        ensures(result == x + 1),
        |&(_, x): &(i64, i64)| -> i64 { x + 1 },
    );
    let g = thrust_macros::closure!(
        requires(*y > 0),
        ensures(result == *y + 1),
        |(_, y): &(i64, i64)| -> i64 { *y + 1 },
    );
    let r = f(&p);
    let s = g(&p);
    assert!(r == s && s == 5);
}
