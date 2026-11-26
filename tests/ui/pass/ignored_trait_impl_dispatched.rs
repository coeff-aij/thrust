//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_trait_impl_dispatched.rs`: an `eq` that is not ignored is checked
// against the trait's spec, which `g`'s reused contract then relies on at `S`.
use thrust_models::Model;
struct S(i32);

impl Model for S {
    type Ty = Self;
}

impl PartialEq for S {
    fn eq(&self, o: &S) -> bool {
        self.0 == o.0
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn g<T: PartialEq + Model>(a: &T) -> bool {
    a == a
}

fn main() {
    let a = S(1);
    let _ = g(&a);
}
