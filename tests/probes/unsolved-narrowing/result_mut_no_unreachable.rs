//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

fn mutate_res(r: &mut Result<i32, i32>) {
    match r {
        Ok(v) => *v += 1,
        Err(e) => *e -= 1,
    }
}

fn main() {
    let mut r = Ok(10);
    mutate_res(&mut r);
    if let Ok(v) = r {
        assert!(v == 11);
    }
}
