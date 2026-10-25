//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of the pass file: `wrap` subtracts one from `cnt`'s result, which leaves `usize` at
// `n = 0`, so its definition fails its check.
#[thrust_macros::logic]
#[thrust_macros::variant(n)]
fn cnt(n: usize) -> usize {
    if n <= 0 {
        0
    } else {
        cnt(n - 1) + 1
    }
}

#[thrust_macros::logic]
fn wrap(n: usize) -> usize {
    cnt(n) - 1
}

#[thrust_macros::ensures(result == wrap(n))]
fn f(n: usize) -> usize {
    cnt_rt(n)
}

fn main() {}

#[thrust_macros::ensures(result == cnt(n))]
fn cnt_rt(n: usize) -> usize {
    if n == 0 { 0 } else { cnt_rt(n - 1) + 1 }
}
