//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// std's `find` returns the first item the predicate accepts: it rejected the items before.
// The closure's contract is written; inferred, PCSat gives no answer within 300 s.
fn main() {
    let v = [1i64, 5, 3, 7];
    match v.iter().find(thrust_macros::closure!(
        requires(true),
        ensures(result == (**x > 4)),
        |x: &&i64| -> bool { **x > 4 },
    )) {
        Some(x) => assert!(*x == 5),
        None => panic!(),
    }
}
