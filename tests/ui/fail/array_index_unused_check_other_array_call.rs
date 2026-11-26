//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// As array_index_unused_check_then_call, with the read on a second array: the unused check of
// `a` is not paired with the read of `b` after the call that changes `b`.

fn zero(a: &mut [i64; 2]) {
    a[0] = 0;
    a[1] = 0;
}

#[thrust_macros::requires(i < 2)]
#[thrust_macros::ensures(result == c[i])]
fn read_other_after_call(c: [i64; 2], i: usize) -> i64 {
    let a = c;
    let mut b = c;
    a[i];
    zero(&mut b);
    b[i]
}

fn main() {}
