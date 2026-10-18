//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_relied_const.rs`: `ig` is analyzed.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

fn ig() -> bool {
    true
}

trait Tr {
    const F: fn() -> bool;
}

impl Tr for S {
    const F: fn() -> bool = ig;
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == true)]
fn h<T: Tr>(_a: &T) -> bool {
    (T::F)()
}

fn main() {
    let s = S(1);
    assert!(h(&s));
}
