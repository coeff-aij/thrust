//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn next<F>(f: &mut F) where F: Fn() {
    f();
}

fn main() {
    let mut f = || { assert!(true); };
    next(&mut f);
}
