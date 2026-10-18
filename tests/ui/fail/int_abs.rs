//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `i32::MIN.abs()` overflows: it panics with overflow checks and returns `i32::MIN` without them,
// so `abs` requires its argument above `i32::MIN`.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn f(x: i32) {
    assert!(x.abs() >= 0);
}

fn main() {
    f(-3);
}
