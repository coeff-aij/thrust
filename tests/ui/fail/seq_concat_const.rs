//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    // wrong: empty.concat(singleton(x)) is singleton(x), not empty
    Seq::<Int>::empty().concat(Seq::singleton(x)) == Seq::<Int>::empty()
)]
fn concat_eq_singleton(x: Int) -> () {
    let _ = x;
}

fn main() {}
