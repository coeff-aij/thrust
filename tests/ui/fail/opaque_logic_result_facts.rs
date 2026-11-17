//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_VERIFY_ONLY=main_with
// `gap` is `#[thrust::opaque]` and no function that reveals it is analyzed here, but its value
// keeps only the fact of its result type, `usize`: `gap(a, b) >= 1` does not follow from it.

mod counts {
    #[thrust_macros::logic]
    #[thrust::opaque]
    pub fn gap(a: usize, b: usize) -> usize {
        if a >= b { a - b } else { 0 }
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(counts::gap(a, b) >= 1)]
fn main_with(a: usize, b: usize) {}

fn main() {
    main_with(3, 5);
}
