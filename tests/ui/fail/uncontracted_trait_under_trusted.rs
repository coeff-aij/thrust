//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// An impl of a trait method without a contract that a trusted generic body calls through its
// bound is checked under `requires(true)`.

trait Tr {
    fn m(&self);
}

struct S;

impl thrust_models::Model for S {
    type Ty = Self;
}

impl Tr for S {
    fn m(&self) {
        assert!(false);
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t<T: Tr>(x: &T) {
    x.m()
}

fn main() {
    t(&S)
}
