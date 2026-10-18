//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_trusted_impl_through_std.rs`: `S`'s `eq` is checked against the trait's spec,
// which `W`'s trusted `eq` relies on at `S`.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

impl PartialEq for S {
    fn eq(&self, o: &S) -> bool {
        self.0 == o.0
    }
}

struct W<T>(T);

impl<T: thrust_models::Model> thrust_models::Model for W<T> {
    type Ty = W<T::Ty>;
}

#[thrust_macros::context]
impl<T: PartialEq + thrust_models::Model> PartialEq for W<T> {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == (*self == *o))]
    fn eq(&self, o: &W<T>) -> bool {
        self.0 == o.0
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t1() {
    let _ = W(S(0)) == W(S(0));
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn a() {
    t1()
}

fn main() {
    let _ = Some(W(S(1))) == Some(W(S(1)));
}
