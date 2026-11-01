//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_VERIFY_ONLY=main
// `h`'s `requires` states the `pre!` of `f`, and `main` passes `f` behind a reference and a second
// value of the closure type in `Wr`. A value behind a reference counts as one of the closure type,
// as the hand-over covers it, so the arguments hold two and the call stops.

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

fn main() {
    let mk = |c: i64| {
        thrust_macros::closure!(
            captures(c: i64),
            requires(x < c || c == 100),
            ensures(true),
            move |x: i64| -> () { assert!(x < c || c == 100); },
        )
    };
    h(&mk(100), Wr(mk(0))); //~ ERROR: a `pre!` stated of one value does not cover another
}
