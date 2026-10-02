//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_TRY_SPECS=1

fn inc(r: Result<i32, u8>) -> Result<i32, u8> {
    let x = r?;
    Ok(x + 1)
}

fn main() {
    assert!(inc(Err(7)) == Err(7));
}
