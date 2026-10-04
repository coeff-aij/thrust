//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=all

// The twin of `fail/int_range_all_add.rs`: below 255 the increment stays in range.
#[thrust::callable]
fn f(x: u8) {
    if x < 255 {
        let y = x + 1;
        assert!(y > x);
    }
}

fn main() {}
