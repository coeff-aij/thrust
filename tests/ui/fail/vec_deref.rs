//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

fn main() {
    let mut v: Vec<i32> = Vec::new();
    Vec::push(&mut v, 10);
    Vec::push(&mut v, 20);
    let s: &[i32] = &v;
    assert!(s[0] == 99); // wrong value → Unsat
}
