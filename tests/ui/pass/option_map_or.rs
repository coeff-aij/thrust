//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::callable]
fn check(opt: Option<i32>) {
    let r = opt.map_or(0, |x| x + 1);
    match opt {
        None => assert!(r == 0),
        Some(i) => assert!(r == i + 1),
    }
}

fn main() {}
