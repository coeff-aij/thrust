//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

const WORD_BITS: usize = 64;

#[thrust_macros::ensures(result * WORD_BITS >= bits && result * WORD_BITS < bits + WORD_BITS)]
fn num_words(bits: usize) -> usize {
    bits.div_ceil(WORD_BITS)
}

fn main() {
    assert!(7u64.div_ceil(8) == 1);
    assert!(16u8.div_ceil(8) == 2);
    assert!(17u32.div_ceil(8) == 3);
}
