//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A tuple's builtin `Clone` runs `W`'s, a crate impl whose generic body runs `S`'s ignored
// `clone`. Trait selection gives each impl's nested obligations, which are followed to the
// ignored body: `q.0 .0 .0` is `0`.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

impl Clone for S {
    #[thrust::ignored]
    fn clone(&self) -> S { //~ ERROR: a verified function can run it
        S(0)
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
