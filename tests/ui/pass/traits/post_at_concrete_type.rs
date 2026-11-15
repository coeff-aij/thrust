//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `post!` of a trait method at a concrete type, written in an `ensures`, takes the contract of
// the impl the path resolves to (std.rs's for `Clone::clone`).

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(thrust_macros::post!(<i32 as Clone>::clone(&x), result))]
fn f(x: i32) -> i32 {
    x.clone()
}

fn main() {
    let y = f(3);
    assert!(y == 3);
}
