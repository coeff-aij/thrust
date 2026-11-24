//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `post!` of an `FnOnce` parameter in a `requires` is an obligation of the caller, which holds
// of a closure that owns a `&mut` whatever its state becomes.
#[thrust_macros::requires(thrust_macros::post!(g(), 1))]
fn take<G: FnOnce() -> i64>(g: G) {}

fn main() {
    let mut n: i64 = 1;
    let r = &mut n;
    take(move || *r);
}
