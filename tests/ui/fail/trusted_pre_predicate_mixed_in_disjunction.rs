//@error-in-other-file: Unknown
//@compile-flags: -C debug-assertions=off
// The program panics, and the solver must not accept it; the query is not Horn, so PCSat answers unknown rather than unsat.
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
