//@error-in-other-file: is `#[thrust::ignored]`
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `g` compares at its type parameter, a call dispatched at each instance of its reused contract.
// `h` calls `g` at its own parameter, so the instance `g::<U>` is still generic and is recorded for
// `h`, whose instance at `S` resolves the call to the ignored, panicking `eq`.

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
