//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_clone_nested.rs`: a `clone` that is not ignored is checked against
// the trait's spec, which the tuple's and `W`'s `clone` rely on.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

impl Clone for S {
    fn clone(&self) -> S {
        S(self.0)
    }
}

struct W<T>(T);

impl<T: thrust_models::Model> thrust_models::Model for W<T> {
    type Ty = W<T::Ty>;
}

impl<T: Clone> Clone for W<T> {
    fn clone(&self) -> W<T> {
        W(self.0.clone())
    }
}

fn main() {
    let p = (W(S(1)), 2);
    let q = p.clone();
    assert!(q.0 .0 .0 == 1);
}
