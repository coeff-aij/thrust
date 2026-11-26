//@compile-flags: -C debug-assertions=off
// The same holds for a bound on an associated type: `<T as Tr>::Assoc: Fn(..)`.

trait Tr { type Assoc; }

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t<T: Tr>(a: T::Assoc) where <T as Tr>::Assoc: Fn(i32) { //~ ERROR: a closure run through a bound on `<T as Tr>::Assoc` cannot have its `pre!` stated
    a(0)
}

fn main() {}
