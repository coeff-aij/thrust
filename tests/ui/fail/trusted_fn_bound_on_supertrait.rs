//@compile-flags: -C debug-assertions=off
// A closure reached only through a supertrait bound (`Y: MyFn` with `MyFn: Fn(..)`) cannot have
// its `pre!` stated either: the `Fn` bound is not written on the parameter.

trait MyFn: Fn(i32) {}
impl<F: Fn(i32)> MyFn for F {}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t<Y: MyFn>(y: Y) { //~ ERROR: a closure run through a bound on `Y` cannot have its `pre!` stated
    y(1)
}

fn main() {}
