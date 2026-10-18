//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `t`'s own `s == s` at `S` is the trusted author's fixed choice, but `*x == *x` at `T = S`
// resolves to the same `S::eq`, which `t`'s contract relies on at `S`: it is verified code.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

impl PartialEq for S {
    #[thrust::ignored]
    fn eq(&self, _o: &S) -> bool { //~ ERROR: a verified function can run it
        assert!(self.0 > 0);
        true
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t<T: PartialEq>(x: &T) {
    let _ = *x == *x;
    let s = S(1);
    let _ = s == s;
}

fn main() {
    t(&S(0))
}
