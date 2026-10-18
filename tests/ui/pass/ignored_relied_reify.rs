//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_relied_reify.rs`: `S`'s `m` is analyzed.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

trait Tr {
    fn m(&self) -> bool;
}

impl Tr for S {
    fn m(&self) -> bool {
        true
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == true)]
#[track_caller]
fn h<T: Tr>(a: &T) -> bool {
    a.m()
}

fn main() {
    let s = S(1);
    let f: fn(&S) -> bool = h::<S>;
    assert!(f(&s));
}
