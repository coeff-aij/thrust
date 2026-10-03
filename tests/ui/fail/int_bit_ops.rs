//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Integer bitwise and shift operators in bodies, computed on bit-vectors of the operand width.

#[thrust_macros::requires(i < 64)]
#[thrust_macros::ensures(result >= 1)]
fn mask(i: usize) -> u64 {
    1 << i
}

#[thrust_macros::requires(x < 256)]
#[thrust_macros::ensures(result < 16)]
fn low_nibble(x: u64) -> u64 {
    x & 15
}

// Thrust's integers carry no upper bound, and the operator is exact only on in-range operands.
#[thrust_macros::requires(x <= u32::MAX)]
#[thrust_macros::ensures(result == x)]
fn xor_twice(x: u32, y: u32) -> u32 {
    (x ^ y) ^ y
}

#[thrust_macros::requires(i == 3)]
#[thrust_macros::ensures(result == 7)]
fn ops(i: usize) -> u64 {
    let m: u64 = 1 << i;
    assert!(m == 8);
    assert!(m | 1 == 9);
    assert!(m >> 2 == 4);
    !m & 15
}

fn main() {
    assert!(mask(63) >= 1);
    assert!(low_nibble(250) < 16);
    assert!(xor_twice(5, 9) == 5);
    assert!(ops(3) == 7);
}
