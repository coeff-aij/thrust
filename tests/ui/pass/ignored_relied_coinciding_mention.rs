//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_relied_coinciding_mention.rs`: `S`'s `eq` is analyzed.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

impl PartialEq for S {
    fn eq(&self, o: &S) -> bool {
        self.0 == o.0
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
