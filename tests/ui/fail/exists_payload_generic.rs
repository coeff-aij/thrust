//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// An `exists` over a constructor's payload in a generic contract, read at an instance: the
// selector the payload is stated by takes the instance's sorts.

use thrust_models::exists;

#[thrust_macros::requires(exists(|v: <T as thrust_models::Model>::Ty| x == Some(v)))]
#[thrust_macros::ensures(Some(result) == x)]
fn known<T: thrust_models::Model + Copy>(x: Option<T>) -> T {
    x.unwrap()
}

fn main() {
    let v = known(None::<i64>);
    assert!(v == 3);
}
