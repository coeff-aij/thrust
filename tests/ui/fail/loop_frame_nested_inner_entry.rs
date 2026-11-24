//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The inner loop is entered after the outer body changes `i`, and keeps what holds of `i` and of
// the unchanged `n` at that entry.

#[thrust_macros::requires(n > 0)]
#[thrust_macros::ensures(true)]
fn f(n: i64) {
    let mut i = 0_i64;
    while i < 3 {
        thrust_macros::invariant!(|i: i64| i >= 0);
        i += 1;
        let mut j = 0_i64;
        while j < 3 {
            thrust_macros::invariant!(|j: i64| j >= 0);
            assert!(i >= 2);
            assert!(n > 0);
            j += 1;
        }
    }
}

fn main() {}
