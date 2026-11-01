//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_VERIFY_ONLY=main,g
// The twin of `fail/closure_trusted_pre_generic_two_params.rs`: `main` runs `g` at a
// `Q` that holds no closure, so `f` is the one value of the closure type, whose `pre!` `h`'s
// `requires` states.

pub trait Call {
    fn call(&self, x: i64);
}

pub struct Wr<F>(F);

pub struct Noop;

impl Call for Noop {
    fn call(&self, _x: i64) {}
}

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

#[thrust_macros::requires(thrust_macros::pre!(f(0)))]
#[thrust_macros::ensures(true)]
fn g<P: Fn(i64), Q: Call>(f: P, q: Q) {
    h(f, q)
}

fn main() {
    let mk = |c: i64| {
        thrust_macros::closure!(
            captures(c: i64),
            requires(x < c),
            ensures(true),
            move |x: i64| -> () { assert!(x < c); },
        )
    };
    g(mk(10), Noop);
}
