//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// `trailing_zeros`/`count_ones` have no bitvector model (integers are plain `Int`), so the only
// fact each carries is its own `<= 64` bound; the two are otherwise independent as far as the
// solver knows, so only their additive bound (128), not the tighter real one (64), follows.

#[thrust_macros::context]
#[thrust_macros::ensures(result <= 128)]
fn bit_counts(x: u64) -> u32 {
    x.trailing_zeros() + x.count_ones()
}

fn main() {}
