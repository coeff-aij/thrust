// Correct verdict: Unsat. The same false claim with no aliasing model in between: the write
// goes through a borrow of `s` directly. It shows the notation is not at fault.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*s == v)]
fn f(s: &mut i64, v: i64) {
    *s = v;
}

fn main() {
    let mut n = 0;
    f(&mut n, 7);
}
