//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// `Option::into_iter` yields the item, then nothing.
fn main() {
    let a: Option<u32> = Some(3);
    let mut it = a.into_iter();
    assert!(it.next() == Some(3));
    assert!(it.next() == None);
}
