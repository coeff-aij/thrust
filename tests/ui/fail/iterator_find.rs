//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn main() {
    let v = [1i64, 5, 3];
    // The closure's contract is written; inferred, PCSat gives no answer for the fail twin
    // within 300 s.
    if let Some(x) = v.iter().find(thrust_macros::closure!(
        requires(true),
        ensures(result == (**x > 4)),
        |x: &&i64| -> bool { **x > 4 },
    )) {
        assert!(*x == 1);
    }
}
