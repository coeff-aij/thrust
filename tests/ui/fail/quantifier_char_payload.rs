//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

// A variable a quantifier binds at an enum holding a `char` ranges over the values whose payload
// is a Unicode scalar value, also without `THRUST_INT_RANGE`, as every value of the enum is.
use thrust_models::forall;

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|o: Option<char>| match o {
            Some(c) => c <= char::MAX,
            None => true,
        }));
    assert!(x == 1);
}
