//@check-pass
//@compile-flags: -C debug-assertions=off

// Integer bitwise and shift operators in bodies, computed on bit-vectors of the operand width.

// Thrust's integers carry no upper bound, and the operator is exact only on in-range operands.
#[thrust_macros::requires(x <= u32::MAX)]
#[thrust_macros::ensures(result == x)]
fn xor_twice(x: u32, y: u32) -> u32 {
    (x ^ y) ^ y
}

fn main() {
    assert!(xor_twice(5, 9) == 5);
}
