//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_VERIFY_ONLY=main,g
// As `fail/closure_trusted_pre_generic_two_params.rs`, with `g` requiring that `f` accepts every
// argument: `main` runs `g` at `Q = Wr<P>`, whose closure rejects the argument `h` calls it with.
// `g` is analyzed at that instance, where the call stops.

pub trait Call {
    fn call(&self, x: i64);
}

pub struct Wr<F>(F);

impl<F: Fn(i64)> Call for Wr<F> {
    #[thrust::trusted]
    #[thrust::callable]
    fn call(&self, x: i64) {
        (self.0)(x)
    }
}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(f(0)))]
#[thrust_macros::ensures(true)]
fn h<P: Fn(i64), Q: Call>(f: P, q: Q) {
    f(0);
    q.call(0);
}

#[thrust_macros::requires(thrust_models::forall(|a: i64| thrust_macros::pre!(f(a))))]
#[thrust_macros::ensures(true)]
fn g<P: Fn(i64), Q: Call>(f: P, q: Q) {
    h(f, q) //~ ERROR: where Thrust cannot follow it
}

fn main() {
    let mk = |c: i64| move |x: i64| { assert!(x < c || c > 5); };
    g(mk(10), Wr(mk(0)));
}
