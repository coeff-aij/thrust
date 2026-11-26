//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A bounds check of a constant-length array whose element is never read, then a call that
// changes the array, then a read of the same index: the unused check is not paired with the read
// after the call, which sees the array as the call left it.

fn zero(a: &mut [i64; 2]) {
    a[0] = 0;
    a[1] = 0;
}

#[thrust_macros::requires(i < 2)]
#[thrust_macros::ensures(result == c[i])]
fn read_after_call(c: [i64; 2], i: usize) -> i64 {
    let mut a = c;
    a[i];
    zero(&mut a);
    a[i]
}

fn main() {}
