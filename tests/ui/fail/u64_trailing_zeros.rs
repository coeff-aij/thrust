//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `trailing_zeros` of 8 is 3, not 2.

#[thrust_macros::requires(w != 0 && w <= 18446744073709551615u64)]
#[thrust_macros::ensures(result == 1)]
fn lowest_bit(w: u64) -> u64 {
    (w >> w.trailing_zeros()) & 1
}

fn main() {
    let x: u64 = 8;
    assert!(x.trailing_zeros() == 2);
    let z: u64 = 0;
    assert!(z.trailing_zeros() == 64);
    let _ = lowest_bit(12);
}
