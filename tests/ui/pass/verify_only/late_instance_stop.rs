//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=caller,h,W::clone

// The twin of `fail/verify_only/late_instance_stop.rs`: with `W::clone` selected, its body, which
// here calls no closure, is checked over its type parameters, and the instance found late needs
// no analysis of its own.

struct W<F>(F);

impl<F> thrust_models::Model for W<F> {
    type Ty = thrust_models::model::Closure<F>;
}

impl<F: FnMut(i32) -> i32 + Clone> Clone for W<F> {
    fn clone(&self) -> Self {
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
        ensures(result == x + 1),
        |x: i32| -> i32 {
            let _k = k;
            x + 1
        },
    );
    let _ = h(&Some(W(c)));
}

fn main() {}
