//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// std.rs's `Option::map` states the closure's `pre!` of the value it holds, as Creusot's does, so
// the call requires it: here the closure is called at 0, which it does not accept.

fn main() {
    let r = Some(0i32).map(|x: i32| {
        assert!(x > 0);
        x + 1
    });
    assert!(r == Some(1));
}
