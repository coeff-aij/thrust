//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=outer,inner
use thrust_models::{forall, model::Closure, Model};

// `g` is checked at each closure it is called with. The selected `outer` runs `inner` at `A` and
// `B`, its second and third type parameters, so the walk checks `g` at `inner`'s closure with
// `outer` as the caller. The closure's contract there is over `outer`'s sorts of `A` and `B`: its
// `post!` in `g`'s precondition gives `first_is` the final values of the captures at those sorts,
// as at `inner`'s own.

#[thrust_macros::predicate]
fn first_is<A: Model<Ty: PartialEq>, B: Model<Ty: PartialEq>>(a: A, b: B) -> bool {
    a == a && b == b
}

#[thrust_macros::requires(forall(|c: Closure<F>, r: i32| thrust_macros::pre!(c(1)) && (!thrust_macros::post!(c(1), r) || r == 1)))]
#[thrust_macros::ensures(true)]
fn g<F: FnMut(i32) -> i32>(mut f: F) -> i32 {
    f(1)
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
