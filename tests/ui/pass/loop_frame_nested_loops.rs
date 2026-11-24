//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The invariant of the inner loop relies on `n`, which neither loop changes.

#[thrust_macros::requires(n > 0)]
#[thrust_macros::ensures(true)]
fn f(n: i64) {
    let mut i = 0_i64;
    while i < 3 {
        thrust_macros::invariant!(|i: i64| i >= 0);
        let mut j = 0_i64;
        while j < 3 {
            thrust_macros::invariant!(|j: i64| j >= 0);
            assert!(n > 0);
            j += 1;
        }
        i += 1;
    }
}

fn main() {}
