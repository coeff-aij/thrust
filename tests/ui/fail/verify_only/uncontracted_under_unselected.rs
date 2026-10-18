//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=main,g
// A function outside the selection with a written contract is trusted, so a selected function
// without a contract that it calls is checked under `requires(true)`.

fn g(x: i32) {
    assert!(x > 0);
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t() {
    g(1)
}

fn main() {
    t()
}
