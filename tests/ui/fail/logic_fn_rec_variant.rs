//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The variant does not decrease at the recursive call, so its termination clause fails.
#[thrust_macros::variant(lo)]
#[thrust_macros::logic]
fn range_sum(lo: i64, hi: i64) -> i64 {
    if lo >= hi {
        0
    } else {
        lo + range_sum(lo + 1, hi)
    }
}

#[thrust_macros::ensures(result == range_sum(lo, hi))]
fn sum_range(lo: i64, hi: i64) -> i64 {
    if lo >= hi {
        0
    } else {
        lo + sum_range(lo + 1, hi)
    }
}

fn main() {}
