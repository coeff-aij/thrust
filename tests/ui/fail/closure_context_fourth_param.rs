//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<T, R, F: Fn(T) -> R>(f: F, x: T) -> R {
    f(x)
}

// As the pass twin, with a closure clause that says nothing of the result, so `g`'s postcondition
// does not follow.
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == d)]
fn g<A: thrust_models::Model, B: thrust_models::Model, C: thrust_models::Model, D: Copy + thrust_models::Model<Ty: PartialEq>>(_a: A, _b: B, _c: C, d: D) -> D {
    apply(thrust_macros::closure!(ensures(true), |x: D| -> D { x }), d)
}

fn main() {
    let r = g(1i64, 2i64, 3i64, 4i64);
    assert!(r == 4);
}
