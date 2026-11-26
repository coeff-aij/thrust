//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A call of the companion written by hand carries the same obligation as the plain recursive call:
// the variant must decrease, so this lemma is not proved.
#[thrust_macros::lemma]
#[thrust_macros::variant(n)]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(false)]
fn bad(n: i64) {
    _thrust_lemma_rec_bad(n) //~ WARN: names the companion of the lemma
}

fn main() {}
