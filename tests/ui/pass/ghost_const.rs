//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::requires(s.len() == 0)]
fn expect_empty(s: Ghost<Seq<Int>>) {
    let _ = s;
}

fn main() {
    let s = thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() });
    expect_empty(s);
}
