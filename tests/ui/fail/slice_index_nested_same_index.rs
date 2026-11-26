//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `s[i][i]` where only the outer `[i]` is known to be in bounds: the bounds check of the inner
// `[i]`, against the length of `s[i]`, can fail.

#[thrust_macros::requires(i < (*s).len())]
#[thrust_macros::ensures(result == (*(*s)[i])[i])]
fn diagonal(s: &[&[i64]], i: usize) -> i64 {
    s[i][i]
}

fn main() {}
