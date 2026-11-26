//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::Model;
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<T, R, F: Fn(T) -> R>(f: F, x: T) -> R {
    f(x)
}

// g has no contract, so it is analyzed at main's instance and the closure at concrete arguments.
#[thrust_macros::context]
fn g<A: Model, B: Model, C: Model, D: Copy + Model<Ty: PartialEq>>(_a: A, _b: B, _c: C, d: D) -> D {
    apply(thrust_macros::closure!(ensures(result == x), |x: D| -> D { x }), d)
}

fn main() {
    let r = g(true, 2i32, 3u8, 7i64);
    assert!(r == 7);
}
