//@error-in-other-file: is `#[thrust::ignored]`
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `g`'s contract is verified once and reused at `S`. Its `==` on `&T` runs std's impl for
// references, whose specification holds only if `T`'s `eq` meets the trait's, which an ignored
// body is not checked against: at `S` the call runs the panicking `eq`.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

impl PartialEq for S {
    #[thrust::ignored]
    fn eq(&self, _o: &S) -> bool {
        assert!(false);
        true
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn g<T: PartialEq + thrust_models::Model>(a: &T) -> bool {
    a == a
}

fn main() {
    let a = S(1);
    let _ = g(&a);
}
