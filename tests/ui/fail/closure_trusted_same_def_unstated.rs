//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// As `fail/closure_trusted_pre_same_def_two_instances.rs`, with `h` stating no `pre!`: `C<u8, ..>`
// is handed over with the obligation to accept every argument, which it meets, and `C<u16, ..>`
// rejects `0`. Both are values of the closure, so the call stops.

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
#[thrust::callable]
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
        assert!(x < c || c == 10);
    };
    k.next_stage(f);
}

fn main() {
    stage::<u16, First>(0, First);
}
