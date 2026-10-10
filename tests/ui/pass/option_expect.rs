//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::requires(x > 0)]
#[thrust_macros::ensures(result == x)]
fn checked(x: i64) -> i64 {
    let o = if x > 0 { Some(x) } else { None };
    o.expect("positive")
}

#[thrust_macros::requires(x > 0)]
#[thrust_macros::ensures(result == x)]
fn checked_result(x: i64) -> i64 {
    let r: Result<i64, i64> = if x > 0 { Ok(x) } else { Err(x) };
    r.expect("positive")
}

fn main() {}
