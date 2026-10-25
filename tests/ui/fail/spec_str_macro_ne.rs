//@compile-flags: -C debug-assertions=off -A unused-variables
//@no-rustfix

// A `!=` written through a macro still meets the `&str`s, which have no model.
macro_rules! differ { ($a:expr, $b:expr) => { $a != $b } } //~ ERROR: can't compare
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(differ!(result, a))] //~ ERROR: the trait bound `str: thrust_models::Model` is not satisfied
fn different(a: &'static str) -> &'static str { if a == "x" { "y" } else { "x" } } //~ ERROR: the trait bound `str: thrust_models::Model` is not satisfied
fn main() { let _ = different("x"); assert!(1 == 2); }

