//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `collect` into a `Vec` holds what the iterator produced up to its completion.

#[thrust_macros::requires(0 < n)]
#[thrust_macros::ensures(true)]
fn range_vec(n: usize) {
    let v: Vec<usize> = (0..n).collect();
    assert!(v.len() == n);
    assert!(v[0] == 0);
}

fn main() {
    range_vec(3);
}
