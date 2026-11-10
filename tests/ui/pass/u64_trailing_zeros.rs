//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER_TIMEOUT_SECS=120

// `trailing_zeros` names the lowest set bit: of 8 it is 3, and of 0 it is 64; of any nonzero
// word, the bit it names is set.
// Z3 takes about 40 s on `lowest_bit`'s goal (a shift by a variable amount), over the default 30 s.

#[thrust_macros::requires(w != 0 && w <= 18446744073709551615u64)]
#[thrust_macros::ensures(result == 1)]
fn lowest_bit(w: u64) -> u64 {
    (w >> w.trailing_zeros()) & 1
}

fn main() {
    let x: u64 = 8;
    assert!(x.trailing_zeros() == 3);
    let z: u64 = 0;
    assert!(z.trailing_zeros() == 64);
    let _ = lowest_bit(12);
}
