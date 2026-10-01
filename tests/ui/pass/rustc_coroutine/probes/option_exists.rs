//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

use thrust_models::exists;

#[thrust_macros::requires(exists(|k: thrust_models::model::UInt| x == Some(k) && k < 5))]
#[thrust_macros::ensures(true)]
fn test(x: Option<usize>) {
    let v = x.unwrap();
    assert!(v < 5);
}

fn main() {
    test(Some(3));
}
