//@compile-flags: -C debug-assertions=off -A unused-variables

// A model may not hold a `&str`: specifications could not tell `S`s apart.
#[derive(Clone, Copy)]
struct S { s: &'static str }
impl thrust_models::Model for S { type Ty = S; } //~ ERROR: the model `S` holds `str`
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result != a)]
fn flip(a: S) -> S { S { s: if a.s == "x" { "y" } else { "x" } } }
fn main() { let _ = flip(S { s: "x" }); assert!(1 == 2); }

