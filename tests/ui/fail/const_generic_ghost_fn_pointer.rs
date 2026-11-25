//@error-in-other-file: takes its const generic parameters as implicit arguments
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(N == 3)]
#[thrust_macros::ensures(result == N)]
fn go<const N: usize>() -> usize { N }
fn main() { let p: fn() -> usize = go::<5>; let r = p(); assert!(r == 4); }
