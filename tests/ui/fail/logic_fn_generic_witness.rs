//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of the pass file: the postcondition is off by one.
#[thrust_macros::logic]
fn pair<T>(t: T, n: usize) -> (usize, T) {
    (n, t)
}

#[thrust_macros::ensures(result == pair::<T>(t, n).0 + 1)]
fn g<T>(t: T, n: usize) -> usize {
    n
}

fn main() {
    let r = g(true, 3);
}
