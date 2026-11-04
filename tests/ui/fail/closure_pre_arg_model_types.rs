//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `pre!` takes each argument at the model of the closure's argument type: an integer literal for
// any integer type, a value for a shared reference to it, a ghost value for its content, and a
// value of a type parameter for that parameter, also where the closure is passed on behind a
// reference (`G = &H`).

use thrust_models::model::Int;
use thrust_models::Ghost;

struct S {
    g: Ghost<Int>,
}

impl thrust_models::Model for S {
    type Ty = S;
}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(0)))]
#[thrust_macros::ensures(true)]
fn apply_literal<G: Fn(i64)>(g: G) {
    g(0)
}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(true)]
fn apply_ref<G: Fn(&i64)>(g: G, x: i64) {
    g(&x)
}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(t)))]
#[thrust_macros::ensures(true)]
fn apply_param<T, G: Fn(T)>(g: G, t: T) {
    g(t)
}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(s.g)))]
#[thrust_macros::ensures(true)]
fn apply_ghost<G: Fn(i64)>(g: G, s: S) {}

#[thrust_macros::requires(thrust_macros::pre!(h(t)))]
#[thrust_macros::ensures(true)]
fn apply_param_by_ref<T, H: Fn(T)>(h: H, t: T) {
    apply_param(&h, t)
}

fn main() {
    apply_ghost(
        |x: i64| assert!(x < 4),
        S {
            g: thrust_macros::ghost!(|| -> Int { 3 }),
        },
    );
    apply_param_by_ref(|x: i64| assert!(x < 5), 4);
    apply_literal(|x: i64| assert!(x < 1));
    apply_ref(|x: &i64| assert!(*x < 2), 1);
    apply_param(|x: i64| assert!(x < 3), 3);
}
