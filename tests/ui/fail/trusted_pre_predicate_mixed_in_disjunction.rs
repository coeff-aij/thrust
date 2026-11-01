//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A predicate that reads `g`'s precondition in both positions states nothing of it, called under a disjunction as well.

fn g(x: i32) {
    assert!(x > 0)
}
#[thrust_macros::predicate]
fn both(x: i32) -> bool {
    (x < 0 || thrust_macros::pre!(g(x))) && !thrust_macros::pre!(g(1))
}
#[thrust::trusted]
#[thrust_macros::requires(x > 100 || both(x))]
#[thrust_macros::ensures(true)]
fn t1(x: i32) {
    g(x)
}

fn main() {
    t1(-1)
}
