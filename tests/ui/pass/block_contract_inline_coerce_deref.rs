//@check-pass
//@compile-flags: -C debug-assertions=off
trait Which { fn which(self) -> i64; }
impl Which for &i64 { fn which(self) -> i64 { 0 } }
impl Which for &&i64 { fn which(self) -> i64 { 1 } }
fn main() {
    let a = 0i64;
    let b = &a;
    let r = &b;
    let v = thrust_macros::block_contract_inline!(
        |r: &&i64| -> i64 requires(true), ensures(result == 1), { r.which() }
    );
    assert!(v == 1);
}
