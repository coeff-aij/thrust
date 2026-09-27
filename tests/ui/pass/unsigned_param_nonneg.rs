//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
fn check(n: usize) {
    assert!(n + 1 >= 1);
}

fn main() {
    check(0);
    check(5);
}
