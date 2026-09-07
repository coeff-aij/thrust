//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result >= 0)]
fn id(n: usize) -> usize {
    n
}

fn main() {
    assert!(id(5) >= 0);
}
