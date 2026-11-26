//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// An `FnMut` closure that captures a function pointer, called by std code (Option::map) through
// its pre!/post!: what the body assumes the pointer returns holds of the pointer the closure is
// built with. Its true twin (asserting `Some(2)`) is rejected: an `FnMut` closure seen from
// outside keeps its captured pointer unrefined, with the contract `true` (documented
// imprecision), so no pass twin exists.
fn inc(x: i64) -> i64 {
    x + 1
}

fn main() {
    let g: fn(i64) -> i64 = inc;
    let mut n = 0i64;
    let c = move |v: i64| -> i64 {
        n += 1;
        g(v)
    };
    let r = Some(1i64).map(c);
    assert!(r == Some(0));
}
