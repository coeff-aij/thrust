//@compile-flags: -C debug-assertions=off -A unused-variables

// A model may not hold a `&str`, in an enum either.
#[derive(Clone, Copy)]
enum E { A(&'static str), B }
impl thrust_models::Model for E { type Ty = E; } //~ ERROR: the model `E` holds `str`
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result != a)]
fn flip(a: E) -> E { match a { E::A("x") => E::A("y"), _ => E::A("x") } }
fn main() { let _ = flip(E::A("x")); assert!(1 == 2); }
