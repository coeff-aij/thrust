//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// The `requires` reads `g`'s precondition positively and negatively, so it is not monotone in it
// and states nothing of it: `g` must accept the argument `t1` passes it.

fn g(x: i32) {
    assert!(x > 0)
}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)) || !thrust_macros::pre!(g(1)))]
#[thrust_macros::ensures(true)]
fn t1(x: i32) {
    g(x)
}

fn main() {
    t1(0)
}
