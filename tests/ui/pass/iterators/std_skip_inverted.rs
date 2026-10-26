//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `Skip` over an inverted range yields nothing; std's `nth` then moves the range to `end..end`,
// where repeated `next` would leave it untouched, so nothing is said of the range afterwards.

fn main() {
    let mut r = 5..3;
    {
        let mut s = r.by_ref().skip(1);
        assert!(s.next().is_none());
    }
}
