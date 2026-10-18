//@check-pass
//@compile-flags: -C debug-assertions=off
// The twin of `fail/uncontracted_trait_under_trusted.rs`.

trait Tr {
    fn m(&self);
}

struct S;

impl thrust_models::Model for S {
    type Ty = Self;
}

impl Tr for S {
    fn m(&self) {
        let _ = self;
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
