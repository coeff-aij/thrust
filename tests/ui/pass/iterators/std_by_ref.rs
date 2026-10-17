//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `by_ref` steps the iterator it borrows: once the reference is gone, the iterator has moved on
// by what the reference produced.

fn main() {
    let mut it = 0..10;
    {
        let r = it.by_ref();
        let a = r.next();
        assert!(matches!(a, Some(0)));
    }
    let b = it.next();
    assert!(matches!(b, Some(1)));
}
