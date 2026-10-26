//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `map` requires the closure to accept every item the inner iterator can hand out, through each
// call it makes: the closure accepts every item of the range.

fn main() {
    let f = thrust_macros::closure!(
        requires(0 <= x && x < 10),
        ensures(result == x),
        |x: i64| -> i64 { x }
    );
    let mut v: Vec<i64> = Vec::new();
    v.extend((0..10).map(f));
}
