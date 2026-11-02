//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// A non-generic trusted function that states `pre!` of a function asks only that of its caller,
// which here passes an argument `g` rejects.

fn g(x: i32) {
    assert!(x > 0)
}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(true)]
fn t1(x: i32) {
    g(x)
}

fn main() {
    t1(0)
}
