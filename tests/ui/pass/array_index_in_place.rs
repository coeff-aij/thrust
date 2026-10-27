//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=1
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An array indexed in place, not through a slice: at a variable index after a bounds check,
// and at a constant one, which `-C opt-level=1` leaves unchecked (`_1[2 of 3]`). The index is
// in bounds by the array's type, also for a parameter, whose value says nothing of its length.
fn set_last(a: &mut [i64]) {
    let n = a.len();
    a[n - 1] = 9;
}

#[thrust::callable]
fn check(i: usize) {
    let mut v = [1i64, 2, 3];
    set_last(&mut v);
    assert!(v[2] == 9);
    if i < 2 {
        assert!(v[i] < 3);
    }
}

#[thrust::callable]
fn third(a: [i64; 3]) -> i64 {
    a[2]
}

fn main() {}
