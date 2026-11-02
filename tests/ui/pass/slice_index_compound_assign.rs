//@check-pass
//@compile-flags: -C overflow-checks=on -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// With overflow checks the read of `s[i]` is in the bounds check's target block and the write
// follows the overflow assert in the next one.
#[thrust_macros::requires(i < (*s).len() && 0 <= (*s)[i] && (*s)[i] < 100)]
#[thrust_macros::ensures((!s)[i] == (*s)[i] + 1 && (!s).len() == (*s).len())]
fn inc(s: &mut [i64], i: usize) {
    s[i] += 1;
}

fn main() {}
