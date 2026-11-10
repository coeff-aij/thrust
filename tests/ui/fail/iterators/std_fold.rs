//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
// The solver took 25.9 s in a timed run of the suite (fptprove ce3cea65b, 6 at a time); 60 s leaves room under load.

// std's `fold` over a range with a concrete closure: the accumulator stays non-negative because
// each call keeps it so, which the client derives from the chain `fold` ensures.
// Fail twin: the closure's contract says nothing more than non-negative.

fn main() {
    let c = thrust_macros::closure!(
        requires(a >= 0),
        ensures(result >= 0),
        |a: i64, x: i64| -> i64 { if x > a { x } else { a } },
    );
    let r = (0..10).fold(0, c);
    assert!(r >= 1);
}
