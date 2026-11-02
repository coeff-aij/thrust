//@check-pass
//@compile-flags: -C debug-assertions=off

// Integer bitwise and shift operators in bodies, computed on bit-vectors of the operand width.
// One function per file: the functions in one query took z3 5.0.0 about 28 s together and well
// under a second apart.

#[thrust_macros::requires(i < 64)]
#[thrust_macros::ensures(result >= 1)]
fn mask(i: usize) -> u64 {
    1 << i
}

fn main() {
    assert!(mask(63) >= 1);
}
