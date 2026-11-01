//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// In an `ensures`, a parameter denotes its argument, also after the body moves it out and assigns
// it again before a loop.

struct S {
    a: i64,
}

impl thrust_models::Model for S {
    type Ty = Self;
}

fn id(x: i64) -> i64 {
    x
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == s.a)]
fn f(mut s: S) -> i64 {
    let t = s;
    s = S { a: id(t.a + 1) };
    let mut k: i64 = 0;
    while k < 1 {
        k += 1;
    }
    s.a
}

fn main() {}
