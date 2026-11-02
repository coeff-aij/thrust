//@check-pass
//@compile-flags: -C debug-assertions=off

// `assume!` is trusted: a false one makes the wrong assertion after it verify. Thrust warns at
// it, and `THRUST_REPORT=functions` lists it.
fn main() {
    let x = 1_i64;
    thrust_macros::assume!(|x: i64| x == 2);
    assert!(x == 2);
}
