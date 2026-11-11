//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `match` of a non-Boolean type in an `ensures` is a value whose last arm reads a payload: it
// is the fallback of the `ite`, taken where the earlier arm does not match, and its selector is
// read only there.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == match r {
    None => d,
    Some(x) => x + 1,
})]
fn succ_or(r: Option<i64>, d: i64) -> i64 {
    match r {
        None => d,
        Some(x) => x + 2,
    }
}

fn main() {
    let n = succ_or(Some(1), 0);
}
