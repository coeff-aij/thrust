//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<T, R, F: Fn(T) -> R>(f: F, x: T) -> R {
    f(x)
}

struct S<T>(T);

// m has no contract, so it is analyzed at main's instance (T = bool, U = i64).
// As the pass twin, asserting a result the closure's clause rules out.
#[thrust_macros::context]
impl<T: thrust_models::Model> S<T> {
    fn m<U: Copy + thrust_models::Model<Ty: PartialEq>>(_t: T, u: U) -> U {
        apply(thrust_macros::closure!(ensures(result == x), |x: U| -> U { x }), u)
    }
}

fn main() {
    let r = S::<bool>::m(true, 5i64);
    assert!(r == 6);
}
