//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `h`'s trusted contract, which `main` relies on at `S`, holds only where the code `T` brings
// meets its specification: a trait object `h` makes of its `T` has `T`'s vtable, and it runs
// `S`'s ignored `m`.

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
fn h<T: Tr + 'static>(a: &T) -> bool {
    let d: &dyn Tr = a;
    d.m()
}

fn main() {
    let s = S(1);
    assert!(h(&s));
}
