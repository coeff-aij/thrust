//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=1
//@rustc-env: THRUST_OPTIMIZED_MIR=1
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// At `-C opt-level=1` and above a constant index reaches MIR as a constant projection
// (`(*_1)[1 of 2]`) instead of an index local.
#[thrust::callable]
fn bump(slice: &mut [i32]) {
    if slice.len() > 1 {
        let before = slice[1];
        slice[1] += 1;
        assert!(slice[1] == before + 1);
    }
}

fn main() {}
