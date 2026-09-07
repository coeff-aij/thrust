//@check-pass
//@compile-flags: -C debug-assertions=off

// The fresh parameter standing for `impl Fn(i64) -> i64` has to line up with the one
// rustc synthesizes for it, which follows the written `T`.
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result >= 0)]
fn h<T>(t: T, n: i64, f: impl Fn(i64) -> i64) -> i64 {
    if n >= 0 {
        n
    } else {
        0
    }
}

fn main() {
    assert!(h(1i32, 3, |x| x) >= 0);
}
