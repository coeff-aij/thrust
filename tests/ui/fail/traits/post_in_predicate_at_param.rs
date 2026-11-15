//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `post!` of a trait method at a type parameter, written in the body of a predicate, takes the
// method's trait-level contract, so a postcondition that contradicts it is refuted.
use thrust_models::Model;
// `f` is verified once over `A`; `post_at_concrete_type_generic.rs` calls a function whose `ensures` names the method at `i32`.

#[thrust_macros::predicate]
fn rel<A: Clone>(x: A, y: A) -> bool {
    thrust_macros::post!(<A as Clone>::clone(&x), y)
}

#[thrust_macros::predicate]
fn rel_outer<A: Clone>(x: A, y: A) -> bool {
    rel::<A>(x, y)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!rel_outer::<A>(x, result))]
fn f<A: Clone + Model>(x: A) -> A {
    x.clone()
}

fn main() {
}
