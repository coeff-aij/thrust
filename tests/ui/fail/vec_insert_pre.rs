//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `Vec::insert` panics when the index is past the end, so a caller that promises nothing fails.
#[thrust::callable]
fn insert_at(v: &mut Vec<u32>, i: usize, x: u32) {
    v.insert(i, x);
}

fn main() {
    let mut v = Vec::new();
    v.push(1u32);
    insert_at(&mut v, 3, 2);
}
