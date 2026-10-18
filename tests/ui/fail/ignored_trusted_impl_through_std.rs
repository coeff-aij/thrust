//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `Option`'s std `eq` runs `W`'s trusted `eq` at `S`, whose contract relies on `S`'s `eq`, an
// ignored one; the trusted `t1` reaching `W::<S>::eq` first does not hide it.

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
