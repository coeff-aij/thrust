//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_VERIFY_ONLY=main_with
// With `THRUST_INT_RANGE`, an opaque logic function keeps the range of its result type, `u8`:
// `widen(a) < 256` holds without its definition.

mod counts {
    #[thrust_macros::logic]
    #[thrust::opaque]
    pub fn widen(a: u8) -> u8 {
        a
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(counts::widen(a) < 256)]
fn main_with(a: u8) {}

fn main() {
    main_with(3);
}
