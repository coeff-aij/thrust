//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The pass twin asserting an item below the last one.

fn count(n: i64) -> i64 {
    let mut c = 0;
    for i in 0..n {
        assert!(i + 1 < n);
        c += 1;
    }
    c
}

fn main() {
    let _ = count(3);
}
