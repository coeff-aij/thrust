//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A call through a reference to a closure, with no contract written: the closure's precondition is inferred.


fn apply<G: Fn(i32) -> i32>(g: G, x: i32) -> i32 {
    g(x)
}


fn main() {
    let k = 3;
    let a = move |x: i32| {
        assert!(x > k);
        x + k
    };
    assert!(apply(&a, 4) == 7);
}
