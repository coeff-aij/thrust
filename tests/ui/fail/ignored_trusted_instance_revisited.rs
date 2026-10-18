//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The trusted `t1` reaches `h::<S>` before `main`'s closure does. `h`'s trusted contract, which
// the closure relies on, holds only where `S`'s `eq` meets the trait's spec, so `h::<S>` is
// followed again when verified code reaches it, and its `==` at `T`, which dispatches on `T`,
// runs the ignored `eq` as verified code.

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
