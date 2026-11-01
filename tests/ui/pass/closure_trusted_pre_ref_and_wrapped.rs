//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_VERIFY_ONLY=main
// The twin of `fail/closure_trusted_pre_ref_and_wrapped.rs`: the second argument holds no
// closure, so `f` behind the reference is the one value of the closure type.

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

fn main() {
    let mk = |c: i64| move |x: i64| { assert!(x < c || c == 100); };
    h(&mk(100), Noop);
}
