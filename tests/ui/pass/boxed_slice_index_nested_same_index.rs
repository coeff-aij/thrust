//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `a[i][i]` of a boxed slice of boxed slices: the check of the inner `[i]`, against the length of
// the slice `a[i]` holds, is paired with the inner level, not with the outer place.

#[thrust_macros::requires(i < a.len() && i < a[i].len())]
#[thrust_macros::ensures(result == a[i][i])]
fn diagonal(a: Box<[Box<[i64]>]>, i: usize) -> i64 {
    a[i][i]
}

fn main() {}
