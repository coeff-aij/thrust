//@compile-flags: -C debug-assertions=off
// A declared bound picks the trait method in the extracted function while the body in place calls
// the inherent method of the same name (at run time `y == 1`).
struct S;
impl S {
    fn get(&self) -> i64 {
        1
    }
}
trait Get {
    fn get(&self) -> i64;
}
impl Get for S {
    fn get(&self) -> i64 {
        2
    }
}
fn main() {
    let s = S;
    let y = thrust_macros::block_contract!(
        <P: Get> |s: P| -> i64
        requires(true),
        ensures(result == 2),
        { s.get() } //~ ERROR: the extracted function would call a different method
    );
    assert!(y == 2);
}
