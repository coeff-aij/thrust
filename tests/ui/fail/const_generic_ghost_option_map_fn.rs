//@error-in-other-file: takes its const generic parameters as implicit arguments
//@compile-flags: -C debug-assertions=off

fn go<const N: usize>(x: usize) -> usize { x + N }
fn main() { let o = Some(1usize).map(go::<3>); assert!(o == Some(5)); }
