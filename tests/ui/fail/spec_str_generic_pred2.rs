//@compile-flags: -C debug-assertions=off -A unused-variables
//@no-rustfix

// A `&str` has no `Model`, so a generic predicate comparing at `T` cannot be applied at it.
#[thrust_macros::predicate]
fn distinct<T: thrust_models::Model>(x: T, y: T) -> bool { x != y }
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(distinct::<&'static str>(result, a))] //~ ERROR: the trait bound `str: thrust_models::Model` is not satisfied
//~^ ERROR: mismatched types
fn different(a: &'static str) -> &'static str { if a == "x" { "y" } else { "x" } } //~ ERROR: the trait bound `str: thrust_models::Model` is not satisfied
fn main() { let _ = different("x"); assert!(1 == 2); }

