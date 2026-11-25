//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_field_of_derive.rs`: `S`'s `eq` is checked against the trait's spec,
// which the derived `eq` of `P` relies on.
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

#[derive(PartialEq)]
struct P(S);

impl Model for P {
    type Ty = P;
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn h<T: PartialEq + Model>(a: &T) -> bool {
    a == a
}

fn main() {
    h(&P(S(1)));
}
