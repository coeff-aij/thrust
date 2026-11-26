//@compile-flags: -C debug-assertions=off
// The clauses are `requires(..)` and `ensures(..)`, by these names.
fn main() {
    let x: i64 = 1;
    let y = thrust_macros::block_contract!(
        |x: i64| -> i64
        ensure(result == 2), //~ ERROR: expected
        { x + 1 }
    );
    assert!(y == 2);
}
