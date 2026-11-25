//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A call of the companion written by hand is allowed, with a warning (asserted in
// fail/lemma_variant_companion_not_decreasing.rs), and proves the lemma when
// the variant decreases.
#[thrust_macros::lemma]
#[thrust_macros::variant(n)]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(n >= 0)]
fn down(n: i64) {
    if n > 0 {
        _thrust_lemma_rec_down(n - 1);
    }
}

fn main() {}
