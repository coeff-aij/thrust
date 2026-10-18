//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `h`'s trusted contract, which `main` relies on at `S`, holds only where the code `T` brings
// meets its specification: verified code takes a function pointer to `h::<S>`, a `#[track_caller]`
// function reached through a shim, and it runs `S`'s ignored `m`.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

trait Tr {
    fn m(&self) -> bool;
}

impl Tr for S {
    #[thrust::ignored]
    fn m(&self) -> bool { //~ ERROR: a verified function can run it
        false
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
