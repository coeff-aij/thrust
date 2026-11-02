//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// In a closure, the formula names the closure's parameters and locals; it is checked under the
// closure's precondition, which the calls establish.
fn main() {
    let inc = |y: i64| -> i64 {
        let z = y + 1;
        thrust_macros::proof_assert!(|z: i64| z >= 2);
        z
    };
    assert!(inc(0) == 1);
}
