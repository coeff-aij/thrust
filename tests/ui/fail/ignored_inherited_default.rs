//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `h`'s trusted contract relies on `T`'s `d`, which at `S` is the ignored default `S` inherits.

trait Tr {
    #[thrust::ignored]
    fn d(&self) -> i32 { //~ ERROR: a verified function can run it
        unimplemented!()
    }
}

struct S;

impl Tr for S {}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn h<T: Tr>(x: &T) -> i32 {
    x.d()
}

fn main() {
    h(&S);
}
