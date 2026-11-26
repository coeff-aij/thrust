//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::Model;
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<T, R, F: Fn(T) -> R>(f: F, x: T) -> R {
    f(x)
}

// A `closure!` clause naming the enclosing function's fourth type parameter: its formula function
// is instantiated at the closure's parent arguments, also when the closure's analyzer holds
// those alone.
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == d)]
fn g<A: Model, B: Model, C: Model, D: Copy + Model<Ty: PartialEq>>(_a: A, _b: B, _c: C, d: D) -> D {
    apply(thrust_macros::closure!(ensures(result == x), |x: D| -> D { x }), d)
}

fn main() {
    let r = g(1i64, 2i64, 3i64, 4i64);
    assert!(r == 4);
}
