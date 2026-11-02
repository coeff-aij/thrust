//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_VERIFY_ONLY=main
// `big` is `#[thrust::opaque]` and no function that reveals it is analyzed here: `main` cannot
// read its definition, so `big(x)` does not give `x > 10`.

mod bounds {
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub fn big(x: i64) -> bool {
        x > 10
    }

    #[thrust::reveal]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(big(result))]
    pub fn make() -> i64 {
        11
    }
}

fn main() {
    let x = bounds::make();
    assert!(x > 10);
}
