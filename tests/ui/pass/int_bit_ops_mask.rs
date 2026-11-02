//@check-pass
//@compile-flags: -C debug-assertions=off

// Integer bitwise and shift operators in bodies, computed on bit-vectors of the operand width.

#[thrust_macros::requires(i < 64)]
#[thrust_macros::ensures(result >= 1)]
fn mask(i: usize) -> u64 {
    1 << i
}

fn main() {
    assert!(mask(63) >= 1);
}
