//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// The tighter, real bound (64) does not follow from the two independent `<= 64` axioms alone.

#[thrust_macros::context]
#[thrust_macros::ensures(result <= 64)]
fn bit_counts(x: u64) -> u32 {
    x.trailing_zeros() + x.count_ones()
}

fn main() {}
