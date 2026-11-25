//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
use thrust_models::exists;
#[thrust_macros::requires(
    opt == None || exists(|i| opt == Some(i) && thrust_macros::pre!(f(i)))
)]
#[thrust_macros::ensures(
    (opt == None && result == None)
    || exists(|i| exists(|j|
        opt == Some(i) && thrust_macros::post!(f(i), j) && result == Some(j)))
)]
fn map<T, U, F>(opt: Option<T>, f: F) -> Option<U>
where
    F: FnOnce(T) -> U,
{
    match opt {
        Some(i) => None,
        None => None,
    }
}

fn main() {}
