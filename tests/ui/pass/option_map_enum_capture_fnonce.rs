//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// The closure of `option_map_enum_capture_fnmut` written in the call, where it is `FnOnce`.
fn main() {
    let mut n: i64 = 0;
    let mut o = Some(&mut n);
    let r = Some(5i64).map(move |v: i64| -> i64 {
        if let Some(x) = &mut o {
            **x += v;
        }
        0
    });
    assert!(r == Some(0));
}
