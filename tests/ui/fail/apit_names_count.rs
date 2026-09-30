//@compile-flags: -C debug-assertions=off

#[thrust_macros::impl_trait_names(A, B)] //~ ERROR: argument-position
fn f(x: &impl Copy) {}

#[thrust_macros::impl_trait_names(T)] //~ ERROR: already a generic parameter
fn g<T>(x: &impl Copy) {}

fn main() {}
