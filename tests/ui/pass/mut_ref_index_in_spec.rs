//@check-pass
//@compile-flags: -C overflow-checks=on -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// In a specification, `s[i]` of a `&mut [T]` is an element of the current value, `(*s)[i]`.
#[thrust_macros::requires(i < s.len() && 0 <= s[i] && s[i] < 100)]
#[thrust_macros::ensures((!s)[i] == s[i] + 1 && (!s).len() == s.len())]
fn inc(s: &mut [i64], i: usize) {
    s[i] += 1;
}

fn main() {}
