//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// std's `fold` over a range with a concrete closure: the accumulator stays non-negative because
// each call keeps it so, which the client derives from the chain `fold` ensures.

fn main() {
    let c = thrust_macros::closure!(
        requires(a >= 0),
        ensures(result >= 0),
        |a: i64, x: i64| -> i64 { if x > a { x } else { a } },
    );
    let r = (0..10).fold(0, c);
    assert!(r >= 0);
}
