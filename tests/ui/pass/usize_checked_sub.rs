//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

fn main() {
    match 5usize.checked_sub(3) {
        Some(d) => assert!(d == 2),
        None => assert!(false),
    }
    match 2usize.checked_sub(3) {
        Some(_) => assert!(false),
        None => {}
    }
}
