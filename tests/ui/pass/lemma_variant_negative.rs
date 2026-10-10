//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The variant must be non-negative where the lemma calls itself, not only decrease.
#[thrust_macros::lemma]
#[thrust_macros::variant(k + 9)]
#[thrust_macros::requires(k >= -10)]
#[thrust_macros::ensures(k >= -10)]
fn down(k: i64) {
    if k > -10 {
        down(k - 1);
    }
}

fn main() {}
