//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=caller THRUST_PER_INSTANCE_GENERICS=1

// Under `THRUST_PER_INSTANCE_GENERICS=1` the body of `g` is checked at each instance a call reaches.
// Outside the selection it is analyzed at the instance std's `Option::map` runs for the selected
// `caller`, which hands it `g::<i64>` as a function item; its assertion fails there.

#[thrust::callable]
fn g<T: Copy>(x: T) -> T {
    let ok = false;
    assert!(ok);
    x
}

#[thrust::callable]
fn caller() {
    let _ = Some(3_i64).map(g::<i64>);
}

fn main() {}
