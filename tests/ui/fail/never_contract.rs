//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A contract on a function that does not return: callers must show the call unreachable.
#[thrust_macros::requires(false)]
fn fail_now(x: u64) -> ! {
    panic!("failed at {x}")
}

fn f(x: u64) -> u64 {
    if x > 3 {
        fail_now(x);
    }
    x
}

fn main() {
    let _ = f(4);
}
