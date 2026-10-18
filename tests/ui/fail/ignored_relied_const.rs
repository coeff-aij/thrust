//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `h`'s trusted contract, which `main` relies on at `S`, holds only where the code `T` brings meets
// its specification: `T::F`, a constant that depends on `T`, is a pointer to the ignored `ig`.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

#[thrust::ignored]
fn ig() -> bool { //~ ERROR: a verified function can run it
    false
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
