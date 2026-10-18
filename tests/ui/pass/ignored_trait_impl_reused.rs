//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_trait_impl_reused.rs`: an `eq` that is not ignored is checked against
// the trait's spec, which the reused contracts of `g` and `h` rely on at `S`.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

impl PartialEq for S {
    fn eq(&self, o: &S) -> bool {
        self.0 == o.0
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn g<T: PartialEq + thrust_models::Model>(a: &T) -> bool {
    *a == *a
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn h<U: PartialEq + thrust_models::Model>(a: &U) -> bool {
    g(a)
}

fn main() {
    let _ = h(&S(1));
}
