//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn sum(s: &[i64], k: usize) -> i64 {
    if k <= 0 {
        0
    } else {
        sum(s, k - 1) + s[k - 1]
    }
}

#[thrust_macros::requires(k <= s.len())]
#[thrust_macros::ensures(result == sum(s, k))]
fn sum_prefix(s: &[i64], k: usize) -> i64 {
    if k == 0 {
        0
    } else {
        sum_prefix(s, k - 1) + s[k - 1]
    }
}

fn main() {}
