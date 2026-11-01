//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// std's `find` returns the first item the predicate accepts, not a later one.
fn main() {
    let v = [1i64, 5, 3, 7];
    match v.iter().find(thrust_macros::closure!(
        requires(true),
        ensures(result == (**x > 4)),
        |x: &&i64| -> bool { **x > 4 },
    )) {
        Some(x) => assert!(*x == 7),
        None => panic!(),
    }
}
