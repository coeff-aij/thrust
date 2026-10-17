//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=all

// The twin of `fail/int_range_all_cast_narrow.rs`: half an `i32` has room for the increment.

#[thrust::callable]
fn f(x: i64) {
    let y = (x as i32) / 2;
    let z = y + 1;
    assert!(z > y);
}

fn main() {}
