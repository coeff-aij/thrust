//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result >= 1)]
fn id(n: usize) -> usize {
    n
}

fn main() {
    assert!(id(5) >= 0);
}
