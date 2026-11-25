//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=caller THRUST_PER_INSTANCE_GENERICS=1

// The trusted generic `tg` calls `g::<i64>` through the constant `F`, a function pointer: the walk
// reads the constant's body at the instance the selected `caller` runs, and analyzes `g` there,
// where its assertion fails.

#[thrust::callable]
fn g<T: Copy>(x: T) -> T {
    let ok = false;
    assert!(ok);
    x
}
const F: fn(i64) -> i64 = g::<i64>;
#[thrust::trusted]
#[thrust::callable]
fn tg<T: Copy>(_x: T) -> i64 {
    F(3)
}
#[thrust::callable]
fn caller() {
    let _ = tg(1_u8);
}
fn main() {}
