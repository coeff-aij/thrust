//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result >= 1)]
fn apply(n: i64, f: impl Fn(i64) -> i64) -> i64 {
    if n >= 0 {
        n
    } else {
        0
    }
}

fn main() {
    assert!(apply(0, |x| x) >= 1);
}
