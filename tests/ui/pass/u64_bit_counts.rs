//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `count_ones` states only its `<= 64` bound and `trailing_zeros` does not count the bits above
// the one it names, so only their additive bound (128), not the tighter real one (64), follows.

#[thrust_macros::context]
#[thrust_macros::ensures(result <= 128)]
fn bit_counts(x: u64) -> u32 {
    x.trailing_zeros() + x.count_ones()
}

fn main() {}
