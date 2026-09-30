//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

// Indexing a slice of a generic element type at `usize` uses the impl's `in_bounds`, although
// the impl needs `T: Model` of the element type parameter.

#[thrust::callable]
fn get<T>(s: &[T], i: usize) -> bool {
    if i < s.len() {
        let _x = &s[i];
        true
    } else {
        false
    }
}

fn main() {}
