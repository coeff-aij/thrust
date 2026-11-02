//@check-pass
//@compile-flags: -C debug-assertions=off

// Integer bitwise and shift operators in bodies, computed on bit-vectors of the operand width.

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
