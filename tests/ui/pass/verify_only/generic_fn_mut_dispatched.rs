//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=caller,h

// `W`'s `m` is checked at each closure it holds, since it is `FnMut`-bounded. The selected generic
// `h` calls it through `T: Tr`, reused by the selected `caller` at `W` holding a closure that returns
// 2 at 1: outside the selection, `m` is analyzed at that instance.

#[thrust_macros::context]
trait Tr {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(true)]
    fn m(&mut self) -> i32;
}

struct W<F>(F);

impl<F> thrust_models::Model for W<F> {
    type Ty = thrust_models::model::Closure<F>;
}

impl<F: FnMut(i32) -> i32> Tr for W<F> {
    fn m(&mut self) -> i32 {
        let r = (self.0)(1);
        assert!(r != 0);
        r
    }
}

#[thrust::callable]
fn h<T: Tr>(mut t: T) -> i32 {
    t.m()
}

#[thrust::callable]
fn caller() {
    let mut n = 0;
    h(W(|x| {
        n += 1;
        x + 1
    }));
}

fn main() {}
