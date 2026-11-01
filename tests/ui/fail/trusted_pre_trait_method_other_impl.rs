//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// `t`'s `requires` states the `pre!` of `<T as Tr>::m`, which at the call is `S::m`. The trusted
// body also runs `U::m`, another impl of the same trait method, whose `pre!` it does not state, so
// `U::m` must accept every argument.
use thrust_models::Model;

trait Tr {
    fn m(&self, x: i32);
}

struct S;
struct U;

impl Model for S {
    type Ty = Self;
}

impl Model for U {
    type Ty = Self;
}

impl Tr for S {
    fn m(&self, x: i32) {
        let _ = (self, x);
    }
}

impl Tr for U {
    fn m(&self, x: i32) {
        let _ = self;
        assert!(x > 0)
    }
}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(<T as Tr>::m(a, x)))]
#[thrust_macros::ensures(true)]
fn t<T: Tr, V: Tr>(a: &T, b: &V, x: i32) {
    a.m(x);
    b.m(x)
}

fn main() {
    t(&S, &U, 0)
}
