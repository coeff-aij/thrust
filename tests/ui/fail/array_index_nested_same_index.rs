//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// One index at two levels of nested arrays: each bounds check, against the constant length of
// its level, is paired with its own level.
#[thrust_macros::requires(i < a.len() && i < a[i].len())]
#[thrust_macros::ensures(result == a[i][i] + a[i][0])]
fn diagonal(a: [[i64; 2]; 2], i: usize) -> i64 {
    a[i][i] + a[i][0]
}

#[thrust_macros::requires(i < a.len() && i < a[i].len())]
#[thrust_macros::ensures(result[i][i] == v)]
fn set_diagonal(mut a: [[i64; 2]; 2], i: usize, v: i64) -> [[i64; 2]; 2] {
    a[i][i] = v;
    a
}

#[thrust_macros::requires(i < s.len())]
#[thrust_macros::ensures(result == s[i][i])]
fn slice_diagonal(s: &[[i64; 3]], i: usize) -> i64 {
    s[i][i]
}

#[thrust_macros::requires(i < s.len() && i < s[i].len())]
fn set_slice_diagonal(s: &mut [[i64; 3]], i: usize, v: i64) {
    s[i][i] = v;
}

fn main() {
    let mut a = [[1i64, 2], [3, 4]];
    let i = 1;
    a[i][i] += 1;
    assert!(a[1][1] == 5);
}
