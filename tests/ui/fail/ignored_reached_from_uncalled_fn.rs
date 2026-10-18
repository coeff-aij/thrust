//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `main` does not call `g`, but `g` is verified, and through `<&S as PartialEq>::eq` it runs
// `S`'s ignored `eq`, whose `false` would fail the assertion. The functions Thrust verifies are
// the roots of the reachability check, not `main` alone.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

impl PartialEq for S {
    #[thrust::ignored]
    fn eq(&self, _o: &S) -> bool { //~ ERROR: a verified function can run it
        false
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn g(a: &S) {
    assert!(a == a);
}

fn main() {}
