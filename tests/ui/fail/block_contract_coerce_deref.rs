//@compile-flags: -C debug-assertions=off
// wrong twin: param `r: &i64` for an outer `&&i64` (deref coercion); inline dispatches to the `&&i64` impl.
trait Which { fn which(self) -> i64; }
impl Which for &i64 { fn which(self) -> i64 { 0 } }
impl Which for &&i64 { fn which(self) -> i64 { 1 } }
fn main() {
    let a = 0i64;
    let b = &a;
    let r = &b;
    let v = thrust_macros::block_contract!( //~ ERROR: is declared
        |r: &i64| -> i64 requires(true), ensures(result == 0), { r.which() }
    );
    assert!(v == 0);
}
