//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A function pointer captured by reference by a closure that another closure captures, the outer
// one called by std code (Option::unwrap_or_else) through its pre!/post!.
fn inc(x: i64) -> i64 {
    x + 1
}

fn main() {
    let g: fn(i64) -> i64 = inc;
    let inner = |v: i64| -> i64 { g(v) };
    let none: Option<i64> = None;
    let r = none.unwrap_or_else(move || inner(2));
    assert!(r == 3);
}
