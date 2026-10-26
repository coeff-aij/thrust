//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Stepping a `&mut Range` past its end leaves the range for later writes through the reference:
// completion fixes the range's value at that call, not its value when the reference dies.

fn main() {
    let mut a = 0..0;
    {
        let mut r = &mut a;
        let x = Iterator::next(&mut r);
        assert!(x.is_none());
        r.start = 7;
    }
    assert!(a.start == 7);
}
