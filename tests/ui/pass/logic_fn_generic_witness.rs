//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A generic logic function whose result `(usize, T)` has facts only in its first part: outside
// its domain its value keeps the body's `T` part, so a type parameter needs no value of its own.
#[thrust_macros::logic]
fn pair<T>(t: T, n: usize) -> (usize, T) {
    (n, t)
}

#[thrust_macros::ensures(result == pair::<T>(t, n).0)]
fn g<T>(t: T, n: usize) -> usize {
    n
}

fn main() {
    let r = g(true, 3);
}
