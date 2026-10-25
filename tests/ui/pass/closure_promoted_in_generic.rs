//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The closure's body holds a promoted constant, the panic message, which names the closure's own
// generic arguments.

fn apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

fn clamp<T>(_t: T, x: i32) -> i32 {
    if x < 0 {
        0
    } else {
        apply(|y| if y >= 0 { y } else { unreachable!("negative") }, x)
    }
}

fn main() {
    assert!(clamp((), 3) == 3);
}
