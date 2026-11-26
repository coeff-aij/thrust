//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// An analyzed function may bound a parameter through a reference: the check on bounds that
// cannot state a `pre!` applies only to functions whose bodies are not analyzed.

fn t<Y>(y: Y) where for<'a> &'a Y: Fn(i32) {
    let _ = &y;
}

fn main() {
    let d = |a: i32| assert!(a > 0);
    t(d);
}
