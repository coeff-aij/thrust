//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=caller THRUST_PER_INSTANCE_GENERICS=1

// Under `THRUST_PER_INSTANCE_GENERICS=1` the body of `g` is checked at each instance a call reaches,
// never over `T`. Outside the selection it is analyzed at the instance the selected `caller`
// makes, where its assertion fails.

#[thrust::callable]
fn g<T: Copy>(x: T, ok: bool) -> T {
    assert!(ok);
    x
}

#[thrust::callable]
fn caller() {
    let _ = g(3_i64, false);
}

fn main() {}
