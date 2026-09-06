//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

use thrust_models::forall;

#[thrust_macros::requires(forall(|i: thrust_models::model::Int|
    (0 <= i && i < (*v).length) ==> (*v).array[i] >= 0))]
#[thrust_macros::ensures(true)]
#[thrust_macros::context]
fn test(v: &Vec<i64>) {
    assert!(v[0] >= 0);
}

fn main() {
    let mut v = Vec::new();
    v.push(1_i64);
    v.push(2);
    v.push(3);
    test(&v);
}
