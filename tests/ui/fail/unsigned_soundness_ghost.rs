//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables

// Soundness check for unsigned facts: under the guard, the ghost term `x - 1` is -1 (model
// arithmetic is unbounded). The ghost value has type `UInt`, whose values are assumed
// non-negative. If the ghost were introduced without an obligation, the contradiction would
// verify `take`'s precondition vacuously; the expected error is the obligation on the term.
use thrust_models::model::UInt;
use thrust_models::Ghost;

#[thrust_macros::requires(g == 0)]
fn take(g: Ghost<UInt>) {
    let _ = g;
}

#[thrust::callable]
fn f(x: usize) {
    if x == 0 {
        let g = thrust_macros::ghost!(|x: usize| -> UInt { x - 1 });
        take(g);
        assert!(x == 0);
    }
}

fn main() {}
