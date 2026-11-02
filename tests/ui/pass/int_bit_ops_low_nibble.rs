//@check-pass
//@compile-flags: -C debug-assertions=off

// Integer bitwise and shift operators in bodies, computed on bit-vectors of the operand width.
// One function per file: the functions in one query took z3 5.0.0 about 28 s together and well
// under a second apart.

#[thrust_macros::requires(x < 256)]
#[thrust_macros::ensures(result < 16)]
fn low_nibble(x: u64) -> u64 {
    x & 15
}

fn main() {
    assert!(low_nibble(250) < 16);
}
