//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

use thrust_models::forall;

#[thrust_macros::requires(n > 0)]
#[thrust_macros::ensures(
    result.len() == n
    && forall(|k: thrust_models::model::Int| (0 <= k && k < n) ==> result[k] == 0)
)]
#[thrust_macros::context]
fn zeros(n: i64) -> Vec<i64> {
    let mut w = Vec::new();
    let mut i = 0_i64;
    while i < n {
        thrust_macros::invariant!(
            |i: i64, w: Vec<i64>, n: i64|
                w.len() == i
                && i <= n
                && forall(|k: thrust_models::model::Int| (0 <= k && k < i) ==> w[k] == 0)
        );
        w.push(1);
        i += 1;
    }
    w
}

fn main() {
    let v = zeros(3);
    assert!(v[0] == 0);
}
