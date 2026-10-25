//@compile-flags: -C debug-assertions=off -A unused-variables

// A `&str` has no `Model`, so a generic contract comparing at `T` cannot be instantiated at it.
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result != a)]
fn other<T: thrust_models::Model + Copy>(a: T, b: T) -> T { b }
fn main() { let _ = other("x", "y"); assert!(1 == 2); } //~ ERROR: the trait bound `str: thrust_models::Model` is not satisfied

