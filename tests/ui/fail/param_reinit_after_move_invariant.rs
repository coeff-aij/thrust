//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A wrong `ensures` about a parameter moved out and assigned again before a loop whose invariant
// replaces the inferred precondition. The invariant does not carry the parameter's current value,
// so the right `ensures` (`s.a + 1`) is not verified either.

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
        thrust_macros::invariant!(|k: i64| k >= 0);
        k += 1;
    }
    s.a
}

fn main() {}
