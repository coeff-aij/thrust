//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:0360cb142

fn next<F>(f: &mut F) where F: Fn() {
    f();
}

fn main() {
    let mut f = || { assert!(true); };
    next(&mut f);
}
