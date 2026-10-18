//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `refl`'s trusted contract holds only where `T`'s `eq` meets the trait's spec. At `S`, whose `eq`
// is ignored and returns `false`, `main`'s assertion fails, so the bounds of a trusted instance
// that verified code runs must not select an ignored impl method.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

impl PartialEq for S {
    #[thrust::ignored]
    fn eq(&self, _o: &S) -> bool { //~ ERROR: relies on its trait's specification through its bounds
        false
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == true)]
fn refl<T: PartialEq + thrust_models::Model>(a: &T) -> bool {
    a == a
}

fn main() {
    let s = S(1);
    assert!(refl(&s));
}
