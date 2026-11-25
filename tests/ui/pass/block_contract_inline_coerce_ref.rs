//@check-pass
//@compile-flags: -C debug-assertions=off
trait Which { fn which(self) -> i64; }
impl Which for &i64 {
    fn which(self) -> i64 { 0 }
}
impl Which for &mut i64 {
    fn which(self) -> i64 { 1 }
}
fn main() {
    let mut a = 0i64;
    let r = &mut a;
    let v = thrust_macros::block_contract_inline!(
        |r: &mut i64| -> i64 requires(true), ensures(result == 1), { r.which() }
    );
    assert!(v == 1);
}
