//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(n > 0)]
fn pred(n: usize) -> usize {
    n - 1
}

fn main() {
    pred(1);
}
