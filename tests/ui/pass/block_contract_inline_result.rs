//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// Thrust has no specification of `Try::branch`, so the result is matched, not used with `?`.
#[thrust_macros::requires(*x >= 0)]
#[thrust_macros::ensures(match result { Ok(v) => v == *x + 1 && !x == v, Err(e) => e == *x && *x > 100 && !x == *x })]
fn step(x: &mut i64) -> Result<i64, i64> {
    let mut y = *x;
    let r = thrust_macros::block_contract_inline!(
        |mut y: i64| -> Result<i64, i64>
        requires(y >= 0),
        ensures(match result { Ok(v) => v == y && v == old!(y) + 1, Err(e) => e == y && y > 100 && y == old!(y) }),
        {
            if y > 100 {
                Err(y)
            } else {
                y += 1;
                Ok(y)
            }
        }
    );
    let r = match r {
        Ok(r) => r,
        Err(e) => return Err(e),
    };
    *x = y;
    Ok(r)
}

fn main() {
    let mut x = 5i64;
    match step(&mut x) {
        Ok(v) => assert!(v == 6),
        Err(_) => assert!(false),
    }
}
