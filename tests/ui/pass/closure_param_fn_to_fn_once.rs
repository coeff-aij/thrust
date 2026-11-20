//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A parameter bounded by `Fn` where it is declared, handed to a function that calls it by value:
// that call is an `Fn` call, so its postcondition is the one `post!` names at the caller.
#[thrust_macros::requires(thrust_macros::pre!(g()))]
#[thrust_macros::ensures(thrust_macros::post!(g(), result))]
fn call_once<G: FnOnce() -> i64>(g: G) -> i64 {
    g()
}

#[thrust_macros::requires(thrust_macros::pre!(f()))]
#[thrust_macros::ensures(thrust_macros::post!(f(), result))]
fn forward<F: Fn() -> i64>(f: F) -> i64 {
    call_once(f)
}

fn main() {}
