//@ignore-on-host: not yet verifiable: PCSat gives no answer within 30 s on fptprove develop c471e831b
//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// std's `chain` collected into a `Vec`: the first range's items, then the second's.
// Fail twin: the third item is the second range's first.

fn main() {
    let v: Vec<i64> = (0..2).chain(5..7).collect();
    assert!(v.len() == 4);
    assert!(v[1] == 1 && v[2] == 2);
}
