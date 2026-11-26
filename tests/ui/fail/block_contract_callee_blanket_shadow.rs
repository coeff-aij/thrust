//@compile-flags: -C debug-assertions=off
// An untyped parameter has no bound, so a blanket impl gives the extracted function a method the
// inherent method of the same name shadows in place: the block would be verified as the call that
// does not run (at run time `y == 1`).
trait K {
    fn k(&self) -> i64 {
        2
    }
}
impl<T> K for T {}
struct S;
impl S {
    fn k(&self) -> i64 {
        1
    }
}
fn main() {
    let s = S;
    let y = thrust_macros::block_contract!(
        |s| -> i64
        requires(true),
        ensures(result == 2),
        { s.k() } //~ ERROR: the extracted function would call a different method
    );
    assert!(y == 2);
}
