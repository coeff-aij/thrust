//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The loop writes through `a`, which keeps only its final value, and leaves `b` as it was.

#[thrust_macros::requires(*a >= 0 && *b == 5)]
#[thrust_macros::ensures(!a >= 10 && !b == 5)]
fn f(a: &mut i64, b: &mut i64) {
    let mut i = 0_i64;
    while i < 10 {
        thrust_macros::invariant!(|i: i64, a: &mut i64| 0 <= i && i <= 10 && *a >= i);
        *a += 1;
        i += 1;
    }
}

fn main() {}
