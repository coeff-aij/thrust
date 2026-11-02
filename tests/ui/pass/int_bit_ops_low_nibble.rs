//@check-pass
//@compile-flags: -C debug-assertions=off

// Integer bitwise and shift operators in bodies, computed on bit-vectors of the operand width.

#[thrust_macros::requires(x < 256)]
#[thrust_macros::ensures(result < 16)]
fn low_nibble(x: u64) -> u64 {
    x & 15
}

fn main() {
    assert!(low_nibble(250) < 16);
}
