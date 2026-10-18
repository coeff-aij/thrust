//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// A function without a contract that a trusted body calls is checked under `requires(true)`.

fn g(x: i32) {
    assert!(x > 0);
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t() {
    g(0)
}

fn main() {
    t()
}
