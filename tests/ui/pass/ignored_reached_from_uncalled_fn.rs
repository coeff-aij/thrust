//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_reached_from_uncalled_fn.rs`: `S`'s `eq` is checked against the trait's
// spec, which `g` relies on through `<&S as PartialEq>::eq`.

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
fn g(a: &S) {
    assert!(a == a);
}

fn main() {}
