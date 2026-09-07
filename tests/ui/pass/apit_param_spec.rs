//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result >= 0)]
fn apply(n: i64, f: impl Fn(i64) -> i64) -> i64 {
    if n >= 0 {
        n
    } else {
        0
    }
}

fn main() {
    assert!(apply(3, |x| x) >= 0);
}
