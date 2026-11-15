//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A closure written in an impl method with a lifetime parameter, whose contract calls a predicate
// with a `post!` in its body: the formula function re-declares the method's parameters before the
// impl's, so the predicate is read at the closure spec's arguments, not at the analysis's.
use thrust_models::Model;

#[thrust_macros::predicate]
fn rel<A: Clone>(x: A, y: A) -> bool {
    thrust_macros::post!(<A as Clone>::clone(&x), y)
}

struct S<T>(T);

#[thrust_macros::context]
impl<T: Model> S<T> {
    fn m<'a, U: Clone + Model>(_t: T, _r: &'a i32, u: U) -> U {
        let g = thrust_macros::closure!(
            requires(true),
            ensures(rel::<U>(x, result)),
            |x: U| -> U { x.clone() },
        );
        g(u)
    }
}

fn main() {
    let _ = S::<bool>::m(true, &0, 5i64);
}
