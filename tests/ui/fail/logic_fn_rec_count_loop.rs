//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn count_nonzero(s: &[i64], k: usize) -> usize {
    if k <= 0 {
        0
    } else {
        count_nonzero(s, k - 1) + if s[k - 1] == 0 { 0 } else { 1 }
    }
}

#[thrust_macros::ensures(result == count_nonzero(s, s.len() - 1))]
fn count(s: &[i64]) -> usize {
    let mut c = 0;
    let mut i = 0;
    while i < s.len() {
        thrust_macros::invariant!(|s: &[i64], i: usize, c: usize| {
            i <= s.len() && c == count_nonzero(s, i)
        });
        if s[i] != 0 {
            c += 1;
        }
        i += 1;
    }
    c
}

fn main() {}
