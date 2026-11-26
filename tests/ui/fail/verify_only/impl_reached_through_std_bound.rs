//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=caller,h

// `W`'s `clone` is `FnMut`-bounded through its impl's parameter, so outside the selection it is
// analyzed at the instances this run's code runs. The selected `h` calls std's `Option::clone`,
// whose body calls `W`'s `clone` at the instance `caller` makes, whose closure returns 0 at 1.

struct W<F>(F);

impl<F> thrust_models::Model for W<F> {
    type Ty = thrust_models::model::Closure<F>;
}

impl<F: FnMut(i32) -> i32 + Clone> Clone for W<F> {
    fn clone(&self) -> Self {
        let mut f = self.0.clone();
        let r = f(1);
        assert!(r != 0);
        W(self.0.clone())
    }
}

#[thrust::callable]
fn h<T: Clone>(t: &Option<T>) -> Option<T> {
    t.clone()
}

#[thrust::callable]
fn caller() {
    let k = 1;
    let c = thrust_macros::closure!(
        requires(true),
        ensures(result == x - 1),
        |x: i32| -> i32 {
            let _k = k;
            x - 1
        },
    );
    let _ = h(&Some(W(c)));
}

fn main() {}
