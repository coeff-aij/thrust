//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_TRY_SPECS=1

fn inc(o: Option<i32>) -> Option<i32> {
    let x = o?;
    Some(x + 1)
}

fn main() {
    if let Some(y) = inc(Some(1)) {
        assert!(y == 3);
    }
    let n: Option<i32> = None;
    if let Some(_) = inc(n) {
        assert!(false);
    }
}
