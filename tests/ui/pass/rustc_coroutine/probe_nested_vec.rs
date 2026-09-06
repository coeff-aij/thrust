//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

use thrust_models::forall;

#[thrust_macros::requires((*v).length > 0)]
#[thrust_macros::requires((*v).array[0].length > 0)]
#[thrust_macros::requires(forall(|i: thrust_models::model::Int| forall(|j: thrust_models::model::Int|
    (0 <= i && i < (*v).length && 0 <= j && j < (*v).array[i].length) ==> (*v).array[i].array[j] >= 0)))]
#[thrust_macros::ensures(true)]
#[thrust_macros::context]
fn test(v: &Vec<Vec<i64>>) {
    assert!(v[0][0] >= 0);
}

fn main() {
    let mut inner = Vec::new();
    inner.push(1_i64);
    inner.push(2);
    let mut v = Vec::new();
    v.push(inner);
    test(&v);
}
