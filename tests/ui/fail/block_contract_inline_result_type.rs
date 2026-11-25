//@no-rustfix
//@compile-flags: -C debug-assertions=off
// wrong twin: `-> i64` is not tied to the body in place; the use site infers i32, so `make` is i32's (1).
trait Make { fn make() -> Self; }
impl Make for i64 { fn make() -> i64 { 0 } }
impl Make for i32 { fn make() -> i32 { 1 } }
fn main() {
    let v: i32 = thrust_macros::block_contract_inline!( //~ ERROR: mismatched types
        || -> i64 requires(true), ensures(result == 0), { Make::make() }
    );
    assert!(v == 0);
}
