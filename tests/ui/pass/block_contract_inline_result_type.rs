//@check-pass
//@compile-flags: -C debug-assertions=off
trait Make { fn make() -> Self; }
impl Make for i64 { fn make() -> i64 { 0 } }
impl Make for i32 { fn make() -> i32 { 1 } }
fn main() {
    let v: i64 = thrust_macros::block_contract_inline!(
        || -> i64 requires(true), ensures(result == 0), { Make::make() }
    );
    assert!(v == 0);
}
