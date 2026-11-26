//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=outer,inner
use thrust_models::{forall, model::Closure, Model};

// The wrong side of `pass/verify_only/per_instance_closure_at_caller_params.rs`: `g` calls the
// closure at 0, which its precondition `x > 0` rules out, at `inner`'s closure, both in `inner`'s
// analysis and at the instance the walk reaches from `outer`.

#[thrust_macros::predicate]
fn first_is<A: Model<Ty: PartialEq>, B: Model<Ty: PartialEq>>(a: A, b: B) -> bool {
    a == a && b == b
}

#[thrust_macros::requires(forall(|c: Closure<F>, r: i32| thrust_macros::pre!(c(1)) && (!thrust_macros::post!(c(1), r) || r == 1)))]
#[thrust_macros::ensures(true)]
fn g<F: FnMut(i32) -> i32>(mut f: F) -> i32 {
    f(0)
}

#[thrust::callable]
#[thrust_macros::context]
fn inner<A: Model<Ty: PartialEq>, B: Model<Ty: PartialEq>>(a: A, b: B) {
    let mut n: i64 = 0;
    let f = thrust_macros::closure!(
        captures(a: &mut A, b: &mut B, n: &mut i64),
        requires(x > 0),
        ensures(result == x && first_is::<A, B>(!a, !b)),
        move |x: i32| -> i32 {
            let _a = &a;
            let _b = &b;
            n += 1;
            x
        },
    );
    g(f);
}

#[thrust::callable]
fn outer<X, A: Model<Ty: PartialEq>, B: Model<Ty: PartialEq>>(x: X, a: A, b: B) {
    inner(a, b);
}

fn main() {}
