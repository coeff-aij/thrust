//@compile-flags: -C debug-assertions=off -A unused-variables
use thrust_models::Model;
// A `&str` has no `Model`, so a generic `requires(a == b)` cannot be instantiated at it.
#[thrust::trusted]
#[thrust_macros::requires(a == b)]
#[thrust_macros::ensures(true)]
fn need_same<T: Model>(a: T, b: T) {}
fn main() { need_same("x", "y"); } //~ ERROR: the trait bound `str: thrust_models::Model` is not satisfied

