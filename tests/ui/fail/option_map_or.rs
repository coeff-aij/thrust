//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// The default no longer matches what `None` maps to.

#[thrust::callable]
fn check(opt: Option<i32>) {
    let r = opt.map_or(1, |x| x + 1);
    match opt {
        None => assert!(r == 0),
        Some(i) => assert!(r == i + 1),
    }
}

fn main() {}
