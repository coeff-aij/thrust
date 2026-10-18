//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_trusted_instance_revisited.rs`: `S`'s `eq` is checked against the trait's spec,
// which `h`'s trusted contract relies on at `S`.

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
#[thrust_macros::ensures(result == true)]
fn h<T: PartialEq + thrust_models::Model>(a: &T) -> bool {
    a == a
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t1() {
    h(&S(0));
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn a() {
    t1()
}

fn main() {
    let c = || {
        let s = S(1);
        assert!(h(&s));
    };
    c();
}
