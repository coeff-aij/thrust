//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() == n + 1)]
fn repeat<T: Clone>(e: T, n: usize) -> Vec<T> {
    vec![e; n]
}

fn main() {
    let v = repeat(7i32, 3);
    assert!(v.len() == 3);
}
