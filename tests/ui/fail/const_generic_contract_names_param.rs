//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(N == 3)] //~ ERROR: cannot mention a const generic parameter
#[thrust_macros::ensures(true)]
fn go<const N: usize>(x: i64) {}

fn main() {}
