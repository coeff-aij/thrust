//@check-pass
//@compile-flags: -C debug-assertions=off
// A `pre!` in a disjunct, as the std specifications guard it, is a precondition the trusted
// function states: its caller discharges `g`'s precondition at `x = 1`.

fn g(x: i32) {
    assert!(x > 0)
}

#[thrust::trusted]
#[thrust_macros::requires(x < 0 || thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(true)]
fn t1(x: i32) {
    g(x)
}

fn main() {
    t1(1)
}
