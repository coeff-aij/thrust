//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A law's proof does not assume the law itself.

use thrust_models::Ghost;
use thrust_models::model::{Int, Seq};

// The `true` entries among the first `k` of `acc`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn trues(acc: Seq<bool>, k: usize) -> Int {
    if k <= 0 {
        0
    } else {
        trues(acc, k - 1) + if acc[k - 1] { 1 } else { 0 }
    }
}

#[thrust_macros::lemma]
#[thrust_macros::law]
#[thrust_macros::ensures(trues(a, k) == 0)]
fn bogus(a: Ghost<Seq<bool>>, k: usize) {}

fn main() {}
