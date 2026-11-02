//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// The function of `option_map_enum_param_fn_item` as a closure.
fn main() {
    let r = Some(Some(3i64)).map(|o: Option<i64>| -> i64 {
        let mut o = o;
        if let Some(x) = &mut o {
            *x += 1;
        }
        0
    });
    assert!(r == Some(0));
}
