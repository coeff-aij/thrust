//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_VERIFY_ONLY=main_with
// `bad`'s definition leaves its result type: `a - b` is negative where `a < b`, so the check of
// its value against `usize` fails. The `:law` its opaque declaration carries (`bad(a, b) >= 0`)
// is assumed only together with that check, so `main_with`'s `ensures`, which the law alone
// proves, does not make the crate verify.

mod counts {
    #[thrust_macros::logic]
    #[thrust::opaque]
    pub fn bad(a: usize, b: usize) -> usize {
        a - b
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(counts::bad(a, b) >= 0)]
fn main_with(a: usize, b: usize) {}

fn main() {
    main_with(3, 5);
}
