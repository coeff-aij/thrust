//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

#[thrust::callable]
fn get<T>(s: &[T], i: usize) -> bool {
    if i <= s.len() {
        let _x = &s[i];
        true
    } else {
        false
    }
}

fn main() {}
