//@compile-flags: -C debug-assertions=off

// The clauses are `requires(..)` and then `ensures(..)`, by these names.
fn main() {
    let x: i64 = 1;
    let y = thrust_macros::block_contract!(
        requires(|x: i64| x == 1),
        ensure(|result: i64| result == 2), //~ ERROR: expected `ensures(..)`
        { x + 1 }
    );
    assert!(y == 2);
}
