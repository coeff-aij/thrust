//@error-in-other-file: takes its const generic parameters as implicit arguments
//@compile-flags: -C debug-assertions=off

struct S<const N: usize>;
impl<const N: usize> S<N> { fn m(x: usize) -> usize { x + N } }
fn main() { let o = Some(1usize).map(S::<3>::m); assert!(o == Some(5)); }
