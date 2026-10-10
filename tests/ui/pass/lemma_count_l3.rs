//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A lemma proved by induction on `k`: the recursive call is the induction hypothesis.

#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn occ(x: usize, s: &[usize], k: usize) -> usize {
    if k <= 0 {
        0
    } else {
        occ(x, s, k - 1) + if s[k - 1] == x { 1 } else { 0 }
    }
}

#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn cnt_lt(s: &[usize], k: usize, b: usize) -> usize {
    if k <= 0 {
        0
    } else {
        cnt_lt(s, k - 1, b) + if s[k - 1] < b { 1 } else { 0 }
    }
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(cnt_lt(s, k, b + 1) == cnt_lt(s, k, b) + occ(b, s, k))]
fn l3(s: &[usize], k: usize, b: usize) {
    if k > 0 {
        l3(s, k - 1, b);
    }
}

fn main() {}
