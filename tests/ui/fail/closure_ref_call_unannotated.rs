//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The closure's assertion fails at the argument of the call through the reference.


fn apply<G: Fn(i32) -> i32>(g: G, x: i32) -> i32 {
    g(x)
}


fn main() {
    let k = 3;
    let a = move |x: i32| {
        assert!(x > k);
        x + k
    };
    apply(&a, 3);
}
