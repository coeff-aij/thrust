//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A boxed slice re-pointed after an unused `b[i]`: the unused check is on the old slice, the read
// after the assignment is paired with its own check, on the new one.

#[thrust_macros::requires(i < a.len() && i < c.len())]
#[thrust_macros::ensures(result == a[i])]
fn repointed(a: Box<[i64]>, c: Box<[i64]>, i: usize) -> i64 {
    let mut b = a;
    b[i];
    b = c;
    b[i]
}

fn main() {}
