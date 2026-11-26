//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `h`'s trusted contract relies on `P`'s derived `eq`, which is not user-trusted and runs the
// field's ignored `eq`.
use thrust_models::Model;
struct S(i32);

impl Model for S {
    type Ty = Self;
}

impl PartialEq for S {
    #[thrust::ignored]
    fn eq(&self, _o: &S) -> bool { //~ ERROR: a verified function can run it
        false
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
