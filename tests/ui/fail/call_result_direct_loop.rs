//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_CALL_RESULT_DIRECT=1

// Each result is the callee's `ensures` at the arguments the call passed: `inc(i)` stays `i + 1`
// of the `i` before `i = a`.
#[thrust_macros::requires(0 <= x && x < 100)]
#[thrust_macros::ensures(result == x + 1)]
fn inc(x: i64) -> i64 {
    x + 1
}

#[thrust_macros::requires(0 <= x && x <= 100)]
#[thrust_macros::ensures(result == 2 * x)]
fn double(x: i64) -> i64 {
    2 * x
}

#[thrust_macros::requires(0 <= x && x <= y)]
#[thrust_macros::ensures(result == y - x)]
fn diff(x: i64, y: i64) -> i64 {
    y - x
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*result == (*p).0 && !result == (!p).0 && (!p).1 == (*p).1)]
fn first(p: &mut (i64, i64)) -> &mut i64 {
    &mut p.0
}

#[thrust_macros::requires(0 <= *x && *x < 100)]
#[thrust_macros::ensures(!x == *x + 1)]
fn bump(x: &mut i64) {
    *x += 1;
}

fn main() {
    let mut p = (0_i64, 5_i64);
    let mut i = 0_i64;
    let mut s = 0_i64;
    let mut q = 0_i64;
    let twice = |x: i64| double(x);
    while i < 10 {
        let a = inc(i);
        let b = twice(a);
        s = diff(a, b);
        i = a;
        let r = first(&mut p);
        *r = s;
        bump(&mut q);
    }
    assert!(s == i + 1 && p.0 == i && p.1 == 5 && q == i);
}
