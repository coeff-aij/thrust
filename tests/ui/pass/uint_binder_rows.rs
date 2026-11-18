//@check-pass
//@compile-flags: -Adead_code -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The rows of a matrix built in a loop, stated with a binder at `usize`.

use thrust_models::forall;

#[thrust_macros::ensures(result.len() == n && forall(|i: usize| !(i < n) || result[i].len() == n))]
fn square(n: usize) -> Vec<Vec<u32>> {
    let mut rows = Vec::new();
    let mut k = 0;
    while k < n {
        thrust_macros::invariant!(|n: usize, k: usize, rows: Vec<Vec<u32>>| {
            k <= n && rows.len() == k && forall(|i: usize| !(i < k) || rows[i].len() == n)
        });
        rows.push(vec![0; n]);
        k += 1;
    }
    rows
}

fn main() {}
