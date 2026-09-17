//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

fn main() {
    let mut r: Result<i32, i32> = Ok(10);
    match &mut r {
        Ok(v) => *v += 1,
        Err(e) => *e -= 1,
    }
    match r {
        Ok(v) => assert!(v == 11),
        Err(_) => unreachable!(),
    }
}
