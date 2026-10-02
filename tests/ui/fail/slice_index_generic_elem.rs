//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

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
