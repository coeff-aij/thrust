//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(n >= 1)]
#[thrust_macros::ensures(result >= 0)]
fn dec(n: usize) -> usize {
    n - 1
}

fn main() {
    assert!(dec(5) >= 0);
}
