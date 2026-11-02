//@check-pass
//@compile-flags: -C debug-assertions=off

// Integer bitwise and shift operators in bodies, computed on bit-vectors of the operand width.
// One function per file: the functions in one query took z3 5.0.0 about 28 s together and well
// under a second apart.

#[thrust_macros::requires(i == 3)]
#[thrust_macros::ensures(result == 7)]
fn ops(i: usize) -> u64 {
    let m: u64 = 1 << i;
    assert!(m == 8);
    assert!(m | 1 == 9);
    assert!(m >> 2 == 2);
    !m & 15
}

fn main() {
    assert!(ops(3) == 7);
}
