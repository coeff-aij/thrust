//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An `Fn` closure that owns a `&mut` only reads through it, so a call that consumes the closure
// leaves the referent as it was.
#[thrust_macros::requires(thrust_macros::pre!(g()))]
#[thrust_macros::ensures(thrust_macros::post!(g(), result))]
fn call_once<G: FnOnce() -> i64>(g: G) -> i64 {
    g()
}

fn main() {
    let mut n: i64 = 1;
    let r = &mut n;
    let c = move || *r;
    let a = call_once(c);
    assert!(a == 1);
    assert!(n == 2);
}
