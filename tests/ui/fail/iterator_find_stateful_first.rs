//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A predicate whose answer depends on its state: it accepts on its second call, not its third.
fn main() {
    let v = [1i64, 5, 3, 7];
    let mut n = 0i64;
    match v.iter().find(thrust_macros::closure!(
        captures(n: &mut i64),
        requires(true),
        ensures(!n == *n + 1 && result == (*n + 1 >= 2)),
        move |_x: &&i64| -> bool { n += 1; n >= 2 },
    )) {
        Some(x) => assert!(*x == 3),
        None => panic!(),
    }
}
