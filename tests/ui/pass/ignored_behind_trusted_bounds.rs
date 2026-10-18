//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_behind_trusted_bounds.rs`: `refl`'s trusted contract holds where `T`'s
// `eq` meets the trait's spec, as `S`'s, which is checked, does.

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
fn refl<T: PartialEq + thrust_models::Model>(a: &T) -> bool {
    a == a
}

fn main() {
    let s = S(1);
    assert!(refl(&s));
}
