//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// A `pre!` on the left of `==>` is not a precondition the trusted function states, so it does not
// exempt `g`.

fn g(x: i32) {
    assert!(x > 0)
}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)) ==> x == 5)]
#[thrust_macros::ensures(true)]
fn t1(x: i32) {
    g(x)
}

fn main() {
    t1(0)
}
