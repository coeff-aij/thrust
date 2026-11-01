//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// One closure written in the generic `stage`, at two instances: `C<u8, ..>` handed to `h` at `P`,
// whose `requires` states its `pre!` of `0`, and `C<u16, ..>` inside `Wr` at `Q`, which the trusted
// `Wr::call` runs at `0`, where it panics. The hand-over covers the closure by its def, so both
// count as values of it, and the call stops.

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

pub trait Next {
    fn next_stage<F: Fn(i64)>(self, f: F);
}

pub struct First;
pub struct Final<G>(G);

impl Next for First {
    fn next_stage<F: Fn(i64)>(self, f: F) {
        stage::<u8, Final<F>>(10, Final(f))
    }
}

impl<G: Fn(i64)> Next for Final<G> {
    fn next_stage<F: Fn(i64)>(self, f: F) {
        h(f, Wr(self.0)) //~ ERROR: a `pre!` stated of one value does not cover another
    }
}

fn stage<T, K: Next>(c: i64, k: K) {
    let f = move |x: i64| {
        let _p: Option<T> = None;
        assert!(x < c);
    };
    k.next_stage(f);
}

fn main() {
    stage::<u16, First>(0, First);
}
