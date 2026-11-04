//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A closure with a written contract that captures a function pointer: its body is checked against
// the contract under the pointer's type, and Option::map reads only the contract.
fn inc(x: i64) -> i64 {
    x + 1
}

fn main() {
    let g: fn(i64) -> i64 = inc;
    let c = thrust_macros::closure!(
        ensures(result == v + 1),
        move |v: i64| -> i64 { g(v) },
    );
    let r = Some(1i64).map(c);
    assert!(r == Some(1));
}
