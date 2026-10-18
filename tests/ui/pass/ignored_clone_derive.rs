//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_clone_derive.rs`: a derived `clone` has the trait's spec where each
// field's `clone` is checked against it.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

impl Clone for S {
    fn clone(&self) -> S {
        S(self.0)
    }
}

#[derive(Clone)]
struct W(S);

impl thrust_models::Model for W {
    type Ty = Self;
}

fn main() {
    let w = W(S(1));
    let v = w.clone();
    assert!(v.0 .0 == 1);
}
