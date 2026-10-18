//@error-in-other-file: is `#[thrust::ignored]`
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A derived `clone`, trusted with the trait's spec, runs each field's `clone`, here an ignored one
// whose body is not checked against the spec: `v.0 .0` is `0`.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

impl Clone for S {
    #[thrust::ignored]
    fn clone(&self) -> S {
        S(0)
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
