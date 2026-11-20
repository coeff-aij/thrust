//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `s[i][i]` indexes both levels with `i`; each level is read through its own bounds check.

#[thrust_macros::requires(i < (*s).len() && i < (*(*s)[i]).len())]
#[thrust_macros::ensures(result == (*(*s)[i])[i])]
fn diagonal(s: &[&[i64]], i: usize) -> i64 {
    s[i][i]
}

fn main() {}
