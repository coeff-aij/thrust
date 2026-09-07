//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The fresh parameter standing for `impl Fn(i64) -> i64` has to line up with the one
// rustc synthesizes for it, which follows the written `T`.
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result >= 1)]
fn h<T>(t: T, n: i64, f: impl Fn(i64) -> i64) -> i64 {
    if n >= 0 {
        n
    } else {
        0
    }
}

fn main() {
    assert!(h(1i32, 0, |x| x) >= 1);
}
