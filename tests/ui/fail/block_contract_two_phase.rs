//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The body of the block contains a two-phase borrow: `v.len()` is read while `&mut v` is reserved.
fn main() {
    let mut v = Vec::new();
    v.push(0usize);
    thrust_macros::block_contract!(
        |mut v: Vec<usize>| -> ()
        requires(v.len() == 1),
        ensures(v.len() == 2 && v[1] == 0),
        {
            v.push(v.len());
        }
    );
    assert!(v.len() == 2);
    assert!(v[1] == 0);
}
