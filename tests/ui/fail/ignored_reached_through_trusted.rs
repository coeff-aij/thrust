//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trusted body may run an ignored function itself, but `t` runs the verified `g` at `S`, and `g`
// relies on `S`'s `eq` meeting the trait's spec; the ignored `eq` returns `false`, so `g`'s
// assertion fails.

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
fn g<T: PartialEq + thrust_models::Model>(a: &T) {
    assert!(a == a);
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t() {
    g(&S(1))
}

fn main() {
    t()
}
