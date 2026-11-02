//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<T, R, F: Fn(T) -> R>(f: F, x: T) -> R {
    f(x)
}

// As the pass twin, with an inner closure clause that says nothing of the result.
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == d)]
fn g<D: Copy + thrust_models::Model<Ty: PartialEq>>(d: D) -> D {
    apply(
        thrust_macros::closure!(ensures(result == x), |x: D| -> D {
            apply(thrust_macros::closure!(ensures(true), |y: D| -> D { y }), x)
        }),
        d,
    )
}

fn main() {
    let r = g(4i64);
    assert!(r == 4);
}
