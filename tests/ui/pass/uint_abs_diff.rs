//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::ensures(result <= a || result <= b)]
fn distance(a: u32, b: u32) -> u32 {
    a.abs_diff(b)
}

#[thrust_macros::requires(a <= b)]
#[thrust_macros::ensures(a + result == b)]
fn gap(a: u64, b: u64) -> u64 {
    a.abs_diff(b)
}

fn main() {
    assert!(7u8.abs_diff(10) == 3);
    assert!(10usize.abs_diff(7) == 3);
    assert!((-3i64).abs_diff(4) == 7u64);
    assert!(5u16.abs_diff(5) == 0);
}
